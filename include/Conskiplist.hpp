#include <iostream>
#include <algorithm>
#include <vector>
#include <limits.h>
#include <math.h>
#include <cfloat>
#include <fstream>
#include <iomanip>
#include <vector>
#include <sstream>
#include <map>
#include <stack>
#include <cstring>
#include <time.h>
#include <queue>
#include <atomic>
#include <assert.h>
#include <random>
#include <mutex>
#include <condition_variable>
#include <folly/MicroLock.h>
#include <shared_mutex>
#include <thread>

#include "util.hpp"

#define PREFETCH(addr, rw, locality) __builtin_prefetch
typedef uint8_t bitmap_t;

typedef unsigned long long KeyType;
typedef unsigned long long VaueType;
typedef long double ModelType; //long double
#define KeyMax (ULLONG_MAX)

#define BITMAP_WIDTH (sizeof(bitmap_t) * 8)
#define BITMAP_SIZE(num_items) (((num_items) + BITMAP_WIDTH - 1) / BITMAP_WIDTH)
#define BITMAP_GET(bitmap, pos) (((bitmap)[(pos) / BITMAP_WIDTH] >> ((pos) % BITMAP_WIDTH)) & 1)
#define BITMAP_SET(bitmap, pos) ((bitmap)[(pos) / BITMAP_WIDTH] |= 1 << ((pos) % BITMAP_WIDTH))
#define BITMAP_CLEAR(bitmap, pos) ((bitmap)[(pos) / BITMAP_WIDTH] &= ~bitmap_t(1 << ((pos) % BITMAP_WIDTH)))
#define BITMAP_NEXT_1(bitmap_item) __builtin_ctz((bitmap_item))

#define p 0.5
#define UNINT_MAX 0xffffffff
#define SkiplistMaxLevel 5
#define Epslion 1e-8
#define LINAERITY 0.8
#define USEPLR 0//now means not use plr's model to rebuild segment 
#define Gm 8 // index layer gamma
#define MAX_DEPTH 6
#define INSERT_ROUTE 0
#define SEGMENT_MAX_SIZE 5e4//5e4//2e4
#define WRITESEG 0
#define DELTA_INSERT 2e5
#define IsREAD_THREAD 1
#define StateType int
#define DEBUG_ASSERT 1
#define PLR_DATA_PREPROCESS 0 //control whether data of plr is preprocessed
#define USINGLinearity 0
#define MEMORY_FETCH 0
#define MERGE_THRESHOLD 5 //when does index node merge buffer and array
#define Threshold_Array 8
#define UTILITY_SMO 0 // utility indicate choose rebuild or split
#define INDEX_DIF 1 //build model with data preprocess(minus minimum key)
#define ITEM_GROUP_SIZE 256
#define SLOT_INIT (4*(ITEM_GROUP_SIZE)) //node slot intital size
#define SPLIT_STATIC 8
#define HIT_THRESHOLD 5

#define LeastSquaresTechniques 0
#define CLOCK_MARK 0

#define STATE_ATOMIC 1
#define CONFLICT_YIELD 0

#define DEBUG 0

// runtime assert
#define RT_ASSERT(expr) \
{ \
    if (!(expr)) { \
        fprintf(stderr, "RT_ASSERT Error at %s:%d, `%s`\n", __FILE__, __LINE__, #expr); \
        exit(0); \
    } \
}
using namespace folly;
using namespace std;

int file_num = 0;
std::mt19937 rd(time(0));
#if CLOCK_MARK
long long rebuild_time[32];
#endif

bool check_file_test(char const *fileName)
{
    // 用 ifstream 来判断文件是否存在
    ifstream testFile(fileName);
    if(!testFile)
    {
        cerr << "file not exit" << endl;
        return false;
    }
    else
    {
        cerr << "file exits" << endl;
        return true;
    }
    return false;
}

bool write_into_file(char const *fileName, char const *content)
{
    ofstream out(fileName,ios::app);
    // ofstream out;
    // out.open(fileName);
    if(!out.is_open())
    {
        cerr << "file not exit" << endl;
        return false;
    }
    else
    {
        out << content;
        // cerr << "write succeed" << endl;
        out.close();
        // usleep(100);
        return true;
    }
    
    return false;
}

bool generate_file_test(char const *fileName)
{
    ofstream out;
    out.open(fileName);
    // 判断文件是否已经打开
    if(out.is_open())
    {
        cerr << "file created succeed" << endl;
        out.close();
        return true;
    }
    else
    {
        cerr << "file created failed" << endl;
        out.close();
        return false;
    }
    
    out.close();
    return false;
}

enum GreedyState {
	Need2 = 0, Need1, Ready
};

enum ItemState {
    Empty = 0, Element, Subtree
};

typedef struct RCUStatus {
    std::atomic<uint64_t> status;
    std::atomic<bool> operating;
    uint64_t waiting_node;
}RCUStatus;

//--------------------------rcu operation--------------------------//
std::unique_ptr<RCUStatus[]> rcu_status;
uint32_t worker_n;
inline void rcu_init(uint32_t worker_n_){
    worker_n = worker_n_;
    rcu_status = std::make_unique<RCUStatus[]>(worker_n);
    for (uint32_t worker_i = 0; worker_i < worker_n; worker_i++) {
        rcu_status[worker_i].status = 0;
        rcu_status[worker_i].operating = false;
        rcu_status[worker_i].waiting_node = 0;
    }
}

inline void rcu_progress(const uint32_t worker_id) {
    rcu_status[worker_id].status++;
}

void rcu_barrier(const uint32_t worker_id){
    uint64_t prev_status[worker_n];
    for (uint32_t w_i = 0; w_i < worker_n; w_i++) {
        prev_status[w_i] = rcu_status[w_i].status;
    }
    for (uint32_t w_i = 0; w_i < worker_n; w_i++) {
        if(worker_id != w_i){
            while (rcu_status[w_i].operating && rcu_status[w_i].status <= prev_status[w_i]){;}
        }
    }
}

inline void rcu_writer_progress(const uint32_t worker_id) {
    rcu_status[worker_id].status++;
}

inline void rcu_write_busy(const uint32_t worker_id){
    rcu_status[worker_id].operating = true;
}

inline void rcu_write_free(const uint32_t worker_id){
    rcu_status[worker_id].operating = false;
}

void rcu_writer_barrier(const uint32_t worker_id){
    uint64_t prev_status[worker_n];
    bool prev_status_w[worker_n];
    for (uint32_t w_i = 0; w_i < worker_n; w_i++) {
        prev_status[w_i] = rcu_status[w_i].status;
        prev_status_w[w_i] = rcu_status[w_i].operating;
    }
    for (uint32_t w_i = 0; w_i < worker_n; w_i++) {
        if(worker_id != w_i){
            while(prev_status_w[w_i] && rcu_status[w_i].operating  && rcu_status[w_i].status <= prev_status[w_i]){
                ;
            }
        }
    }
}

template<class K, class V,class M>
class skiplist {
    public:
        class Point {
        public:
            M x;
            M y;

            Point();

            Point(M x0, M y0) {
                x = x0;
                y = y0;
            }

            M slope_to(Point *other){
                return (this->y - other->y) / (this->x - other->x);
            }

            std::pair<M,M> line_to(Point *other){
                M a = this->slope_to(other);
                M b = -a * this->x + this->y;
                return {a,b};
            }            

            Point* upper_bound(M gamma) {
                Point* res = new Point(this->x, this->y + gamma);
                return res;
            }

            Point* lower_bound(M gamma) {
                Point* res = new Point(this->x, this->y - gamma);
                return res;
            }
        };

        class Line {
        public:
            M slope;
            M intercept;

            Line();

            Line(M a,M b):slope(a),intercept(b){}

            Line(Point* a, Point* b) {
                this->slope = (b->y - a->y) / (b->x - a->x);
                this->intercept = b->y - b->x * this->slope;
            }

            M at(KeyType x){
                return slope * (static_cast<long double>(x)) + intercept;
            }

            Point* Intersection(Line* b) {
                M x,y;
                M deta = this->slope - b->slope;
                x = (b->intercept - this->intercept)/deta;
                y = (this->slope * b->intercept - this->intercept*b->slope)/deta;
                Point* res = new Point(x, y);
                return res;
            }

            //point k above line
            bool AboveAssert(Point* k) {
                return k->y > k->x * this->slope + this->intercept;
            }

            //point k below line
            bool BeblowAssert(Point* k) {
                return k->y < k->x * this->slope + this->intercept;
            }

        };

        class Segment {
            public:
                K start;
                K stop;
                M slope;
                M intercept;
                Segment();
                Segment(K start, K stop, M slope, M intercept) {
                    this->start = start;
                    this->stop = stop;
                    this->slope = slope;
                    this->intercept = intercept;
                }
        };

        class GreedyPLR {
        public:
            GreedyState state = GreedyState::Need2;
            int gamma;
            Point* s0 = nullptr;
            Point* s1 = nullptr;
            Point* sint = nullptr;//point of intersection
            Point* s_last = nullptr;
            Line* rho_lower = nullptr;
            Line* rho_upper = nullptr;

            GreedyPLR();

            GreedyPLR(int ga):gamma(ga){}

            void setup(Point* s0, Point* s1)
            {
                this->s0 = s0;
                this->s1 = s1;

                this->rho_lower = new Line(s0->upper_bound(this->gamma), s1->lower_bound(this->gamma));

                this->rho_upper = new  Line(s0->lower_bound(this->gamma), s1->upper_bound(this->gamma));
                this->sint = nullptr;
                this->sint = this->rho_upper->Intersection(this->rho_lower);
                if (this->sint == nullptr) {
                    cerr << "there is no intersection between upper line and lower line " << endl;
                    RT_ASSERT(this->sint != nullptr);
                }
            };

            Segment* CurrentSegment(M end) {
                if (this->state != GreedyState::Ready) {
                    return nullptr;
                }
                Segment* res = nullptr;
                M s_start = this->s0->x;
                M s_stop = end;
                M s_slope;
                s_slope = (this->rho_lower->slope + this->rho_upper->slope) / 2.0;
                M s_intercept = this->sint->y - this->sint->x * s_slope;
                res = new Segment(s_start, s_stop, s_slope, s_intercept);
                return res;
            }

            Segment* Process_pt(Point* k) {
                if (this->state != GreedyState::Ready) {
                    return nullptr;
                }
                if (!(this->rho_lower->AboveAssert(k) && this->rho_upper->BeblowAssert(k))) {
                    //重新开一个段
                    Segment* current = this->CurrentSegment(this->s_last->x);//(k->x);
                    // delete this->s0;
                    k->y = 0;
                    k->x = 0;
                    // this->s0 = nullptr;
                    this->s0 = k;
                    // this->s_last = nullptr;
                    this->s_last = k;
                    this->state = GreedyState::Need1;

                    return current;
                }
                Point* s_u = k->upper_bound(this->gamma);
                Point* s_l = k->lower_bound(this->gamma);
                if (this->rho_upper->BeblowAssert(s_u)) {
                    delete this->rho_upper;
                    // this->rho_upper = nullptr;
                    this->rho_upper = new Line(this->sint, s_u);
                }

                if (this->rho_lower->AboveAssert(s_l)) {
                    delete this->rho_lower;
                    // this->rho_lower = nullptr;
                    this->rho_lower = new Line(this->sint, s_l);
                }
                return nullptr;

            }

            Segment* Process(M x, M y) {
                //delete this->s_last;
                Segment* res = nullptr;
                Point* newp = new Point(x, y);
                // GreedyState newState = this->state;
                if (this->state == GreedyState::Need2) {
                    this->s0 = nullptr;
                    this->s_last = nullptr;
                    newp->y = 0;
                    this->s_last = newp;
                    this->s0 = newp;
                    // newState = GreedyState::Need1;
                    this->state = GreedyState::Need1;
                }
                else if (this->state == GreedyState::Need1) {
                    //delete this->s1;
                    this->s1 = nullptr;
                    this->s_last = nullptr;
                    this->s_last = newp;
                    this->s1 = newp;
                    this->setup(this->s0, this->s1);
                    // newState = GreedyState::Ready;
                    this->state = GreedyState::Ready;
                }
                else if (this->state == GreedyState::Ready) {
                    res = this->Process_pt(newp);
                    if (res != nullptr) {
                        // newState = GreedyState::Need1;
                        this->state = GreedyState::Need1;
                    }
                    else {
                        // newState = GreedyState::Ready;
                        this->state = GreedyState::Ready;
                    }
                }
                // this->state = newState;
                return res;
            }

            Segment* finish() {
                if (this->state == GreedyState::Need2) {
                    return nullptr;
                }
                else if (this->state == GreedyState::Need1) {
                    Segment* curnt = new Segment(this->s0->x, KeyMax, 0.0, this->s0->y);
                    // cerr <<"finish slopt:"<< curnt->slope << " "<<endl;
                    return curnt;
                }
                else if (this->state == GreedyState::Ready) {
                    return this->CurrentSegment(KeyMax);
                }
                return nullptr;
            }
                        
            void greedy(KeyType *data,int data_size,
                    vector<std::pair<M,M>> &models,vector<int> &pivot_id){// int error_bound,
                int remain_size = data_size;
                int offset = 0;
                // cout<<"total sum:"<<remain_size<<endl;
                while(remain_size > 1){
                    KeyType *keys_ = data + offset;
                    Line model(0.0,0.0);
                    int new_segment_size = greedy_spline_corridor(keys_,remain_size,model);
                    if(new_segment_size == 0){
                        RT_ASSERT(remain_size == 1);
                    }
                    pivot_id.push_back(offset);
                    models.push_back({model.slope,model.intercept});
                    offset += (new_segment_size);
                    remain_size -= new_segment_size;
                }
            }

            //返回本次分段加入了多少点
            int greedy_spline_corridor(KeyType *data,int remain_size,Line &model){// int error_bound
                if(remain_size < 2)
                    return 0;
                
                Point pt1(data[0],0);
                Point pt2(data[1],1);

                if(remain_size == 2){
                    std::pair<M,M> l_ = pt1.line_to(&pt2);
                    model.slope = l_.first, model.intercept = l_.second;
                    return 2;
                }

                M upper = pt1.line_to(pt2.upper_bound(gamma)).first;
                M lower = pt1.line_to(pt2.lower_bound(gamma)).first;

                for(int i = 2;i<remain_size;i++){
                    Point pt(data[i],i);

                    std::pair<M,M> l_ = pt1.line_to(&pt);
                    Line l(l_.first,l_.second);
                    if(l.slope > upper || l.slope < lower){
                        model.slope = (upper + lower)/2.0;
                        model.intercept = -(model.slope) * data[0];
                        return i+1;
                    }
                    
                    M potential_upper = pt1.line_to(pt.upper_bound(gamma)).first;

                    M potential_lower = pt1.line_to(pt.lower_bound(gamma)).first;

                    if(potential_upper < upper){
                        upper = potential_upper;
                    }
                    if(potential_lower > lower){
                        lower = potential_lower;
                    }
                }
                model.slope = (upper + lower)/2.0;
                model.intercept = -(model.slope) * data[0];
                return remain_size-1;

            }

            //建模时每个key减去本段最小的key       
            void greedy_dif(KeyType *data,int data_size,
                    vector<std::pair<M,M>> &models,vector<int> &pivot_id){// int error_bound,
                int remain_size = data_size;
                int offset = 0;
                // cout<<"total sum:"<<remain_size<<endl;
                while(remain_size > 1){
                    KeyType *keys_ = data + offset;
                    Line model(0.0,0.0);
                    int new_segment_size = greedy_spline_corridor_dif(keys_,remain_size,model);
                    if(new_segment_size == 0){
                        RT_ASSERT(remain_size == 1);
                    }
                    pivot_id.push_back(offset);
                    models.push_back({model.slope,model.intercept});
                    offset += (new_segment_size);
                    remain_size -= new_segment_size;
                }
            }

            //建模时每个key减去本段最小的key     
            //返回本次分段加入了多少点
            int greedy_spline_corridor_dif(KeyType *data,int remain_size,Line &model){// int error_bound
                if(remain_size < 2)
                    return 0;
                KeyType pivot_v = data[0];

                Point pt1(data[0] - pivot_v,0);
                Point pt2(data[1] - pivot_v,1);

                if(remain_size == 2){
                    std::pair<M,M> l_ = pt1.line_to(&pt2);
                    model.slope = l_.first, model.intercept = l_.second;
                    return 2;
                }

                M upper = pt1.line_to(pt2.upper_bound(gamma)).first;
                M lower = pt1.line_to(pt2.lower_bound(gamma)).first;

                for(int i = 2;i<remain_size;i++){
                    Point pt(data[i] - pivot_v,i);

                    std::pair<M,M> l_ = pt1.line_to(&pt);
                    Line l(l_.first,l_.second);
                    if(l.slope > upper || l.slope < lower){
                        model.slope = (upper + lower)/2.0;
                        //TODO 可能可以换一个交叉点
                        return i+1;
                    }
                    
                    M potential_upper = pt1.line_to(pt.upper_bound(gamma)).first;

                    M potential_lower = pt1.line_to(pt.lower_bound(gamma)).first;

                    if(potential_upper < upper){
                        upper = potential_upper;
                    }
                    if(potential_lower > lower){
                        lower = potential_lower;
                    }
                }
                model.slope = (upper + lower)/2.0;
                return remain_size-1;

            }

        };

        typedef struct spinlock {
            std::atomic<bool> lock_ = {0};

            bool GetValue() noexcept {
                return lock_.load(std::memory_order_acquire);
            }

            void lock() noexcept {
                for (;;) {
                // Optimistically assume the lock is free on the first try
                if (!lock_.exchange(true, std::memory_order_acquire)) {
                    return;
                }
                // Wait for lock to be released without generating cache misses
                while (lock_.load(std::memory_order_acquire)) {
                    // Issue X86 PAUSE or ARM YIELD instruction to reduce contention between
                    // hyper-threads
                    __builtin_ia32_pause();
                }
                }
            }

            bool try_lock() noexcept {
                // First do a relaxed load to check if lock is free in order to prevent
                // unnecessary cache misses if someone does while(!try_lock())
                return !lock_.load(std::memory_order_acquire) &&
                    !lock_.exchange(true, std::memory_order_acquire);
            }

            void unlock() noexcept {
                lock_.store(false, std::memory_order_release);
            }

        }slock;
        struct node{
            K key;
            V value;
        };
        struct SNode{            
            SNode* Next() {
                // Use an 'acquire load' so that we observe a fully initialized
                // version of the returned Node.
                return (next_.load(std::memory_order_acquire));
            }

            void SetNext(SNode* x) {
                next_.store(x, std::memory_order_release);
            }

            bool CASNext(SNode* expected, SNode* x) {
                return next_.compare_exchange_strong(expected, x);
            }

            bool isIndexNode(){
                return isIndex;
            }

            inline void AppendNext(SNode* next_left,SNode* next_right){
                SNode *pre_cur = this;
                RT_ASSERT(pre_cur->Key < next_left->Key);
                while (true){
                    SNode *pr_next = pre_cur->Next();//1.暂存当前Index的next
                    //检查next left和next right 位于 pre_cur与pr_next之间
                    if(pre_cur->Key < next_left->Key && (!pr_next || pr_next->Key > next_right->Key)){
                        next_right->SetNext(pr_next);//2.将next的后继修改为pr_next
                        if(pre_cur->CASNext(pr_next,next_left)){//3.compare and set
                            return;
                        }
                        //4.false then loop
                    }else if(pr_next && pr_next->Key < next_left->Key){
                        pre_cur = pr_next;
                    }else{
                        //key的位置incorrect
                        RT_ASSERT(0);
                    } 
                }
            }

            K Key;//the lower bound
            bool isIndex; //read only, true-> index node, false -> sgement node
            std::atomic<SNode*> next_; // next 指针用于构建链表，直接继承 
            SNode(K base,bool type):Key(base),isIndex(type),next_(nullptr){}  
        };
        struct inode{
            K key;
            SNode *address;
        };      
        static bool cmp(inode a,inode b){
            return a.key <= b.key;
        }
        struct inodeArray{
            std::allocator<inode> inodes_allocator;
            inode* new_inodes(int n){
                inode* x = inodes_allocator.allocate(n);
                if(x!=nullptr){
                    return x;
                }
                std::cout<<"allocate failed"<<std::endl;
                return nullptr;
            }
            void delete_inodes(inode* x, int n){
                inodes_allocator.deallocate(x, n);
            }

            inline int predict(K key){
                M v = (slope) * (static_cast<long double>(key)) + (intercept);
                if(v > std::numeric_limits<int>::max() / 2) {
                    return size - 1;
                }
                if(v < 0 || static_cast<int>(v)<0){
                    return 0;
                }
                return std::min(size - 1, static_cast<int>(v));
            }
			
			long long SpaceSize(){
                long long space_size = sizeof(inodeArray);
                space_size += (sizeof(inode) * size);
                return space_size;
            }

            M slope = 0,intercept = 0;
            int size;
            inode* iArray;
            inodeArray(int size_, M slope_,M intercept_,inode *iArray_) :slope(slope_), intercept(intercept_),size(size_), iArray(iArray_){}
            inodeArray(int size_, M slope_,M intercept_):slope(slope_), intercept(intercept_),size(size_){
                iArray = nullptr;
                iArray = new_inodes(size_);
            }
            inodeArray(M slope_,M intercept_,K key,SNode *value):slope(slope_), intercept(intercept_),size(1){
                iArray = nullptr;
                iArray = new_inodes(1);
                iArray[0] = {key,value};
            }
            ~inodeArray(){
                if(iArray){
                    delete_inodes(iArray,size);
                    iArray = nullptr;
                }
            }
        };
        struct subtree;
        struct Item{
            union {
                node data;
                subtree* child;
            }comp;
            Item(){}
            Item(K key, V value){
                this->comp.data.key = key;
                this->comp.data.value = value;
            }
        };
        struct subtree{
            inline bool isOrderedArray(){
                return ordered_array;
            }

            //--------------------------model operation--------------------------//
            inline int predict(K key){
                M v = (static_cast<long double>(this->slope)*1000.0) * (static_cast<long double>(key))/1000.0 + (static_cast<long double>(this->intercept));
                if(v > std::numeric_limits<int>::max() / 2) {
                    return this->num_items - 1;
                }
                if(v < 0 || static_cast<int>(v)<0){
                    return 0;
                }
                return std::min(this->num_items - 1, static_cast<int>(v));
            }
            
            //return 满足>（position-1）及之前的item的 最小的key
            K GetRangeBound(int position){
                //TODE DEBUG
                position = min(position,num_items-1);
                if(position < intercept){//为什么会有position<intercep? 说明该position不会有key，该部分应该被舍弃
                    return 0;
                }
                //random pick a key
                if(BITMAP_GET(none_bitmap,position-1) == 0){
                    //pick from left
                    if(BITMAP_GET(child_bitmap,position-1) == 0){
                        return GetItemAt(position-1).comp.data.key+1;
                    }else{
                        subtree *n = GetItemAt(position-1).comp.child;
                        while(1){
                            if(n->ordered_array){
                                int n_key_size = n->size.load();
                                return n->GetItemAt(n_key_size-1).comp.data.key + 1;
                            }else{
                                for(int ps = n->num_items-1;ps>=0;ps--){
                                    if(BITMAP_GET(n->none_bitmap,ps) == 0){
                                        if(BITMAP_GET(n->child_bitmap,ps) == 0){
                                            return n->GetItemAt(ps).comp.data.key + 1;
                                        }else{
                                            n = n->GetItemAt(ps).comp.child;
                                            break;
                                        }
                                    }
                                }
                            }
                            
                        }
                    }
                }
                else if(BITMAP_GET(none_bitmap,position) == 0){
                    //pick from right
                    if(BITMAP_GET(child_bitmap,position) == 0){
                        return GetItemAt(position).comp.data.key;
                    }else{
                        subtree *n = GetItemAt(position).comp.child;
                        while(1){
                            if(n->ordered_array){
                                return n->GetItemAt(0).comp.data.key;
                            }else{
                                for(int ps = 0;ps<n->num_items-1;ps++){
                                    if(BITMAP_GET(n->none_bitmap,ps) == 0){
                                        if(BITMAP_GET(n->child_bitmap,ps) == 0){
                                            return n->GetItemAt(ps).comp.data.key;
                                        }else{
                                            n = n->GetItemAt(ps).comp.child;
                                            break;
                                        }
                                    }
                                }
                            } 
                        }
                    }
                }
                else{//random pick one
                //因为model的问题，可能多个key映射一个position，也可能key十分分散，position空隙极大
                //对于后者，无法直接使用模型，还是需要读取前一个区域或者后一个区域中最后或最前的数据
                    K bound_res = ceil((static_cast<long double>(position) - intercept)/(slope));
                    int predict_pos = predict(bound_res);
                    if(predict_pos == position || predict_pos == position-1){
                        return bound_res;
                    }
                    if(BITMAP_GET(none_bitmap,predict_pos)){
                        return bound_res;
                    }
                    RT_ASSERT(predict_pos > position);
                    if(BITMAP_GET(child_bitmap,predict_pos) == 0){
                        return bound_res;
                    }else{
                        subtree *n = GetItemAt(predict_pos).comp.child;
                        while(1){
                            if(n->ordered_array){
                                return n->GetItemAt(0).comp.data.key;
                            }else{
                                for(int i = 0;i<n->num_items;i++){
                                    if(BITMAP_GET(n->none_bitmap,i) == 0){
                                        if(BITMAP_GET(n->child_bitmap,i) == 0){
                                            return n->GetItemAt(i).comp.data.key;
                                        }else{
                                            n = n->GetItemAt(i).comp.child;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // while(1){
                    //     int predict_pos = predict(bound_res);
                    //     if(predict_pos == position || predict_pos == position-1){
                    //         return bound_res;
                    //     }
                    //     if(BITMAP_GET(none_bitmap,predict_pos) || BITMAP_GET(child)){
                    //         return bound_res;
                    //     }
                    //     if(predict_pos > position){
                    //         bound_res-=1;
                    //     }else{
                    //         bound_res+=1;
                    //     }
                    // }
                }

                // K bound_res = (static_cast<long double>(position) - intercept)/(slope * 1000.0)*1000.0;
                // int check_pos = predict(bound_res);
                // //bound_res >= real
                // if(check_pos >= position){
                //     if(predict(max(uint64_t(bound_res-16),uint64_t(0))) >= position){
                //         //need 指数搜索
                //         K right_b = max(uint64_t(bound_res-16),uint64_t(0));
                //         K left_b = (static_cast<long double>(position-1) - intercept)/(slope * 1000.0)*1000.0;
                //         //find a range where p(left_b)<=position p(right_b)>=position
                //         while(left_b + 16 < right_b){
                //             K mid = left_b + ((right_b - left_b)>>1);
                //             if(predict(mid) >= position){
                //                 right_b = mid;
                //             }else{//p(mid)<position
                //                 left_b = mid;
                //             }
                //         }
                //         bound_res = right_b;
                //     }
                //     //probe
                //     //p(bound_res) >= position
                //     K probe = bound_res-1;
                //     while(predict(probe) >= position){
                //         probe --;
                //     }
                //     bound_res = probe+1;
                // }else{
                //     //bound_res < real
                //     //check_pos < position
                //     K afterward = min(bound_res+16,KeyMax);
                //     if(predict(afterward) < position ){
                //         //need 指数搜索
                //         K left_b = afterward;
                //         K right_b = (static_cast<long double>(position+1) - intercept)/(slope * 1000.0)*1000.0;
                //         while(left_b + 16 < right_b){
                //             K mid = left_b + ((right_b - left_b)>>1);
                //             if(predict(mid) < position){
                //                 left_b = mid;
                //             }else{
                //                 right_b = mid;
                //             }
                //         }
                //         bound_res = left_b;
                //     }
                //     //probe
                //     K probe = bound_res+1;
                //     while(predict(probe) < position){
                //         probe ++;
                //     }
                //     bound_res = probe;
                // }
                // return bound_res;
            }

            void CheckBound(K start_key,K stop_key){
                //smallest
                subtree *n = this;
                bool flag = false;
                while(1){
                    if(n->ordered_array){
                        RT_ASSERT(n->GetItemAt(0).comp.data.key >= start_key);
                        break;
                    }else{
                        for(int i = 0;i<n->num_items;i++){
                            if(BITMAP_GET(n->none_bitmap,i) == 0){
                                if(BITMAP_GET(n->child_bitmap,i) == 0){
                                    RT_ASSERT(n->GetItemAt(i).comp.data.key >= start_key);
                                    flag = true;
                                    break;
                                }else{
                                    n = n->GetItemAt(i).comp.child;
                                    break;
                                }
                            }
                        }
                        if(flag)
                            break;
                    }
                }

                //biggest
                n = this;
                flag = false;
                while(1){
                    if(n->ordered_array){
                        int size_n = n->size.load();
                        RT_ASSERT(n->GetItemAt(size_n-1).comp.data.key < stop_key);
                        break;
                    }else{
                        for(int i = n->num_items-1;i>=0;i--){
                            if(BITMAP_GET(n->none_bitmap,i) == 0){
                                if(BITMAP_GET(n->child_bitmap,i) == 0){
                                    RT_ASSERT(n->GetItemAt(i).comp.data.key < stop_key);
                                    flag = true;
                                    break;
                                }else{
                                    n = n->GetItemAt(i).comp.child;
                                    break;
                                }
                            }
                        }
                        if(flag)
                            break;
                    }
                }
            }

            //--------------------------item array(without model) operation--------------------------//
            int BinarySearch(int size,K key){
                int l = 0, r = size-1;
                int res = -1;
                while (l <= r){
                    int mid = l + (r-l)/2;
                    K mid_key  = GetItemAt(mid).comp.data.key;
                    if(mid_key == key){
                        return mid;
                    }
                    else if(key < mid_key){
                        r = mid-1;
                    }else{
                        res = mid;
                        l = mid + 1;
                    }
                }
                return res;
            }

            bool BinarySearch(int size,K key,V &value){
                int l = 0, r = size-1;
                int res = -1;
                V res_value;
                while (l <= r){
                    int mid = l + (r-l)/2;
                    K mid_key  = GetItemAt(mid).comp.data.key;
                    if(mid_key == key){
                        value = GetItemAt(mid).comp.data.value;
                        return true;
                    }
                    else if(key < mid_key){
                        r = mid-1;
                    }else{
                        res = mid;
                        res_value = GetItemAt(mid).comp.data.value;
                        l = mid + 1;
                    }
                }
                if(res >= 0 ){
                    value = res_value;
                    return true;
                }else{
                    return false;
                }
            }

            bool BinarySearch_debug(int size,K key,V &value,int &skip){
                int l = 0, r = size-1;
                int res = -1;
                V res_value;
                while (l <= r){
                    int mid = l + (r-l)/2;
                    K mid_key  = GetItemAt(mid).comp.data.key;
                    if(mid_key == key){
                        value = GetItemAt(mid).comp.data.value;
                        return true;
                    }
                    else if(key < mid_key){
                        r = mid-1;
                    }else{
                        res = mid;
                        res_value = GetItemAt(mid).comp.data.value;
                        l = mid + 1;
                        skip++;
                    }
                }
                if(res >= 0 ){
                    value = res_value;
                    return true;
                }else{
                    return false;
                }
            }
            
            bool insert_array(int size,K key,V value){
                int res = BinarySearch(size,key);
                if(res>=0 && GetItemAt(res).comp.data.key == key){
                    return false;
                }
                RT_ASSERT(res < 0 || GetItemAt(res).comp.data.key < key);
                for(int pos = size-1;pos>res;pos--){
                    FillItemAt(pos+1,GetItemAt(pos));
                    // items[pos+1] = items[pos];
                }
                FillItemAt(res+1,Item(key,value));
                //check
                for(int i = 1;i<=size;i++){
                    if(GetItemAt(i).comp.data.key <= GetItemAt(i-1).comp.data.key){
                        cout<<"insert_array error"<<endl;
                    }
                }
                BITMAP_CLEAR(none_bitmap,size);
                this->size.fetch_add(1, std::memory_order_acquire);
                return true;
            }

            //--------------------------subtree operation--------------------------//

            inline Item GetItemAt(int position){
                return ItemMatrix[position / ITEM_GROUP_SIZE][position % ITEM_GROUP_SIZE];
            }

            inline void SetChildAt(int position,subtree *new_ad){
                ItemMatrix[position / ITEM_GROUP_SIZE][position % ITEM_GROUP_SIZE].comp.child = new_ad;
                // __atomic_store_n(&(ItemMatrix[position / ITEM_GROUP_SIZE][position % ITEM_GROUP_SIZE].comp.child),new_ad, __ATOMIC_SEQ_CST);
            }

            inline void FillItemAt(int position,Item it_local){
                this->ItemMatrix[position / ITEM_GROUP_SIZE][position % ITEM_GROUP_SIZE] = it_local;
            }
            
            //traverse with lock
            std::pair<bool,V> find_key_in_subtree_pessimistic(K key){
                subtree* n = this;
                int pos = n->predict(key);
                while(!n->TryLockItem(pos)){
                    // printf("try lock %lld 's %d item failed\n",n,pos);
                }
                while(1){
                    if (BITMAP_GET(n->none_bitmap, pos) == 1) {
                        //checkTypeEqualNull
                        n->ReleaseItem(pos);
                        break;
                    }
                    else if(BITMAP_GET(n->child_bitmap, pos) == 0){
                        //checkTypeEqualData
                        Item it = n->GetItemAt(pos);
                        bool res_1 = it.comp.data.key == key;
                        V res_2 = it.comp.data.value;
                        n->ReleaseItem(pos);
                        return {res_1,res_2};
                    }
                    else{
                        subtree* next_subtree = n->GetItemAt(pos).comp.child;
                        if(next_subtree->ordered_array){
                            const int sub_node_size = next_subtree->size.load(std::memory_order_acquire);
                            V res_2;
                            bool res_1 = next_subtree->BinarySearch(sub_node_size,key,res_2);
                            n->ReleaseItem(pos);
                            return {res_1,res_2};
                        }else{
                            n->ReleaseItem(pos);
                            int pos_next = next_subtree->predict(key);
                            while(!next_subtree->TryLockItem(pos_next)){
                                // printf("try lock %lld 's %d item failed\n",next_subtree,pos_next);
                            }
                            n = next_subtree;
                            pos = pos_next;
                        } 
                    }
                }
                return {false,0};
            }

            std::pair<bool,V> find_key_in_subtree_debug(K key,int &depth){
                subtree* n = this;
                int pos = n->predict(key);
                while(!n->TryLockItem(pos)){
                    // printf("try lock %lld 's %d item failed\n",n,pos);
                }
                while(1){
                    if (BITMAP_GET(n->none_bitmap, pos) == 1) {
                        //checkTypeEqualNull
                        n->ReleaseItem(pos);
                        break;
                    }
                    else if(BITMAP_GET(n->child_bitmap, pos) == 0){
                        //checkTypeEqualData
                        bool res_1 = n->GetItemAt(pos).comp.data.key == key;
                        V res_2 = n->GetItemAt(pos).comp.data.value;
                        n->ReleaseItem(pos);
                        return {res_1,res_2};
                    }
                    else{
                        depth++;
                        subtree* next_subtree = n->GetItemAt(pos).comp.child;
                        if(next_subtree->ordered_array){
                            const int sub_node_size = next_subtree->size.load(std::memory_order_acquire);
                            int find_pos = next_subtree->BinarySearch(sub_node_size,key);
                            if(find_pos >= 0){
                                Item it = next_subtree->GetItemAt(find_pos);
                                bool res_1 = it.comp.data.key == key;
                                V res_2 = it.comp.data.value;
                                n->ReleaseItem(pos);
                                return {res_1,res_2};
                            }else{
                                n->ReleaseItem(pos);
                                return {false,0};
                            }
                        }else{
                            n->ReleaseItem(pos);
                            int pos_next = next_subtree->predict(key);
                            while(!next_subtree->TryLockItem(pos_next)){
                                // printf("try lock %lld 's %d item failed\n",next_subtree,pos_next);
                            }
                            n = next_subtree;
                            pos = pos_next;
                        } 
                    }
                }
                return {false,0};
            }

            //traverse without lock
            std::pair<bool,V> find_key_in_subtree_optimistic(K key){
                subtree* n = this;
                while(1){
                    int pos = n->predict(key);
                    Item fetch_value;
                    bool none_bitmap_state,child_bitmap_state;
                    while(1){
                        none_bitmap_state = BITMAP_GET(n->none_bitmap, pos);
                        child_bitmap_state =  BITMAP_GET(n->child_bitmap, pos);
                        fetch_value = n->GetItemAt(pos);
                        if( n->CheckLockfree(pos) 
                            && ( none_bitmap_state == BITMAP_GET(n->none_bitmap, pos) ) 
                            && ( child_bitmap_state ==  BITMAP_GET(n->child_bitmap, pos) )
                        ){
                            //这里可能与update一致性冲突 
                            break;
                        }
                    }

                    if(none_bitmap_state == 1){
                        return {false,0};
                    }else if(child_bitmap_state == 0){
                        return {fetch_value.comp.data.key == key,fetch_value.comp.data.value};
                    }else{
                        subtree* next_subtree = fetch_value.comp.child;
                        if(next_subtree->ordered_array){
                            //if next_subtree is ordered array then need to get the lock
                            while(!n->TryLockItem(pos)){;}
                            //check again
                            next_subtree = n->GetItemAt(pos).comp.child;
                            if(next_subtree->ordered_array){
                                const int sub_node_size = next_subtree->size.load(std::memory_order_acquire);
                                V res_2;
                                bool res_1 = next_subtree->BinarySearch(sub_node_size,key,res_2);
                                n->ReleaseItem(pos);
                                return {res_1,res_2};
                            }
                            n->ReleaseItem(pos);
                        }
                        n = next_subtree;
                    }
                }
            }

            std::pair<bool,V> find_key_in_subtree_optimistic_debug(K key,int &depth,int &binary_skip){
                subtree* n = this;
                while(1){
                    depth++;
                    int pos = n->predict(key);
                    Item fetch_value;
                    bool none_bitmap_state,child_bitmap_state;
                    while(1){
                        none_bitmap_state = BITMAP_GET(n->none_bitmap, pos);
                        child_bitmap_state =  BITMAP_GET(n->child_bitmap, pos);
                        fetch_value = n->GetItemAt(pos);
                        if( n->CheckLockfree(pos) 
                            && ( none_bitmap_state == BITMAP_GET(n->none_bitmap, pos) ) 
                            && ( child_bitmap_state ==  BITMAP_GET(n->child_bitmap, pos) )
                        ){
                            //这里可能与update一致性冲突 
                            break;
                        }
                    }

                    if(none_bitmap_state == 1){
                        return {false,0};
                    }else if(child_bitmap_state == 0){
                        return {fetch_value.comp.data.key == key,fetch_value.comp.data.value};
                    }else{
                        subtree* next_subtree = fetch_value.comp.child;
                        if(next_subtree->ordered_array){
                            //if next_subtree is ordered array then need to get the lock
                            while(!n->TryLockItem(pos)){;}
                            //check again
                            next_subtree = n->GetItemAt(pos).comp.child;
                            if(next_subtree->ordered_array){
                                const int sub_node_size = next_subtree->size.load(std::memory_order_acquire);
                                V res_2;
                                bool res_1 = next_subtree->BinarySearch_debug(sub_node_size,key,res_2,binary_skip);
                                n->ReleaseItem(pos);
                                return {res_1,res_2};
                            }
                            n->ReleaseItem(pos);
                        }
                        n = next_subtree;
                    }
                }
            }

            //non-lock
            std::pair<bool,V> find_key_in_subtree_nonlock(K key){
                subtree* n = this;
                int pos = n->predict(key);
                while(1){
                    if (BITMAP_GET(n->none_bitmap, pos) == 1) {
                        //checkTypeEqualNull
                        break;
                    }
                    else if(BITMAP_GET(n->child_bitmap, pos) == 0){
                        //checkTypeEqualData
                        bool res_1 = n->GetItemAt(pos).comp.data.key == key;
                        V res_2 = n->GetItemAt(pos).comp.data.value;
                        return {res_1,res_2};
                    }
                    else{
                        subtree* next_subtree = n->GetItemAt(pos).comp.child;
                        if(next_subtree->ordered_array){
                            const int sub_node_size = next_subtree->size.load(std::memory_order_acquire);
                            int find_pos = next_subtree->BinarySearch(sub_node_size,key);
                            if(find_pos >= 0){
                                Item it = next_subtree->GetItemAt(find_pos);
                                bool res_1 = it.comp.data.key == key;
                                V res_2 = it.comp.data.value;
                                return {res_1,res_2};
                            }else{
                                return {false,0};
                            }
                        }else{
                            int pos_next = next_subtree->predict(key);
                            n = next_subtree;
                            pos = pos_next;
                        } 
                    }
                }
                return {false,0};
            }

            //non-lock
            std::pair<bool,V> find_key_in_subtree_nonlock_debug(K key,int &depth){
                subtree* n = this;
                int pos = n->predict(key);
                while(1){
                    if (BITMAP_GET(n->none_bitmap, pos) == 1) {
                        //checkTypeEqualNull
                        break;
                    }
                    else if(BITMAP_GET(n->child_bitmap, pos) == 0){
                        //checkTypeEqualData
                        bool res_1 = n->GetItemAt(pos).comp.data.key == key;
                        V res_2 = n->GetItemAt(pos).comp.data.value;
                        return {res_1,res_2};
                    }
                    else{
                        depth++;
                        subtree* next_subtree = n->GetItemAt(pos).comp.child;
                        if(next_subtree->ordered_array){
                            const int sub_node_size = next_subtree->size.load(std::memory_order_acquire);
                            V res_2;
                            bool res_1 = next_subtree->BinarySearch(sub_node_size,key,res_2);
                            return {res_1,res_2};
                        }else{
                            int pos_next = next_subtree->predict(key);
                            n = next_subtree;
                            pos = pos_next;
                        } 
                    }
                }
                return {false,0};
            }

            //return the # of key in subtree
            //递归式调用
            int ScanKeys(K low_bound,int key_num,std::vector<std::pair<K,V>> &result){
                int real_scan_cnt = 0;
                int pos = predict(low_bound);
                while(real_scan_cnt < key_num && pos < num_items){
                    LockItem(pos);//get lock before read data
                    int lock_p = pos/BITMAP_WIDTH;
                    while(lock_p >= int(pos/BITMAP_WIDTH) && pos < num_items){
                        if (BITMAP_GET(none_bitmap, pos) == 0) {
                            if(BITMAP_GET(child_bitmap, pos) == 0){
                                K key_p = GetItemAt(pos).comp.data.key;
                                if(key_p >= low_bound){
                                    result.push_back({key_p,GetItemAt(pos).comp.data.value});
                                    real_scan_cnt++;
                                }
                            }else{
                                subtree *next = GetItemAt(pos).comp.child;
                                int scan_size = next->ScanKeys(low_bound,key_num - real_scan_cnt,result);
                                real_scan_cnt += scan_size;
                            }
                        }
                        pos++;
                    }
                    ReleaseItem(lock_p*BITMAP_WIDTH);
                }
                return real_scan_cnt;
            }

            //--------------------------CC--------------------------//
            inline bool CheckLockfree(int n){
                return this->mlock[n/BITMAP_WIDTH].GetValue() == false;
            }


            inline bool TryLockItem(int n){
                // printf("try to lock %lld 's %d item\n",this,n);
                return this->mlock[n/BITMAP_WIDTH].try_lock();
            }

            //get the lock of n->items[pos]
            inline void LockItem(int n){
                this->mlock[n/BITMAP_WIDTH].lock();
                // printf("lock %lld 's %d item\n",this,n);
            }

            //release the lock of n->items[pos]
            inline void ReleaseItem(int n){
                this->mlock[n/BITMAP_WIDTH].unlock();
                // printf("unlock %lld 's %d item\n",this,n);
            }

            //--------------------------subtree statistic--------------------------//
            long long SpaceSize(){
                long long res = sizeof(is_two) + sizeof(size) + sizeof(num_items) + sizeof(bitmap_t*)*2;
                if(ordered_array){
                    return res;
                }
                res += (sizeof(M)*2);
                // long long child_cnt = 0;
                // const int bitmap_size_ = BITMAP_SIZE(num_items);
                // res += (sizeof(bitmap_t) * bitmap_size_ * 2);
                // res += (sizeof(Item) * num_items);
                for(int i = 0;i<num_items;i++){
                    if(BITMAP_GET(none_bitmap,i) == 0){
                        if(BITMAP_GET(child_bitmap,i) == 1){
                            Item it = GetItemAt(i);
                            res += ((GetItemAt(i).comp.child)->SpaceSize());
                            // child_cnt++;
                        }
                    }
                }
                return res;
            }

            bool is_two = 0; // is special node for only two keys
            bool ordered_array = 0;// indicate model-based or ordered array
            std::atomic<int> size;
            int num_items = 0; // size of items
            M slope = 0,intercept = 0;
            int matrixRow;
            Item **ItemMatrix=nullptr;
            // Item* items = nullptr;
            slock *mlock = nullptr;
            bitmap_t* none_bitmap = nullptr; // 1 means None, 0 means Data or Child
            bitmap_t* child_bitmap = nullptr; // 1 means Child. will always be 0 when none_bitmap is 1

            subtree(bool is_two_,bool is_ordered_array,int size_,int num_items_):is_two(is_two_),
                ordered_array(is_ordered_array),size(size_),num_items(num_items_){}
            subtree(bool is_two_,bool is_ordered_array,int size_):is_two(is_two_),
                ordered_array(is_ordered_array),size(size_){}

        };
        struct Segment_pt: SNode{
            //--------------------------allocator---------------------------//
            std::allocator<subtree> subtree_allocator;
            subtree* new_subtree(int n){
                subtree* x = subtree_allocator.allocate(n);
                if(x!=nullptr){
                    return x;
                }
                std::cout<<"allocate failed"<<std::endl;
                return nullptr;
            }
            void delete_subtree(subtree* x,int n){
                subtree_allocator.deallocate(x,n);
            }
            void destroy_subtree(subtree* root){
                std::stack<subtree*> s;
                s.push(root);
                while (!s.empty()) {
                    subtree* n = s.top(); s.pop();
                    for (int i = 0; i < n->num_items; i ++) {
                        if (BITMAP_GET(n->child_bitmap, i) == 1) {
                            s.push(n->GetItemAt(i).comp.child);
                        }
                    }
                    int slot_num = n->num_items;
                    for(int items_i = 0;items_i<n->matrixRow;items_i++){
                        Item *items_ = n->ItemMatrix[items_i];
                        if(items_i < n->matrixRow-1){
                            delete_items(items_,ITEM_GROUP_SIZE);
                            slot_num-=ITEM_GROUP_SIZE;
                        }   
                        else{
                            delete_items(items_,slot_num);
                        }
                        n->ItemMatrix[items_i] = nullptr;
                    }
                    delete_itemsMatrix(n->ItemMatrix,n->matrixRow);
                    // delete_items(n->items, n->num_items);
                    const int bitmap_size = BITMAP_SIZE(n->num_items);
                    delete_bitmap(n->none_bitmap, bitmap_size);
                    delete_bitmap(n->child_bitmap, bitmap_size);
                    delete_slock(n->mlock,bitmap_size);
                    delete_subtree(n, 1);
                }
            }
            std::allocator<Item*> itemMatrix_allocator;
            Item** new_itemMatrix(int n){
                Item **x = itemMatrix_allocator.allocate(n);
                RT_ASSERT(x);
                return x;
            }
            void delete_itemsMatrix(Item** x, int n)
            {
                itemMatrix_allocator.deallocate(x, n);
            }

            std::allocator<Item> item_allocator;
            Item* new_items(int n)
            {
                Item* x = item_allocator.allocate(n);
                if(x!=nullptr){
                    return x;
                }
                std::cout<<"allocate failed"<<std::endl;
                return nullptr;
            }
            void delete_items(Item* x, int n)
            {
                item_allocator.deallocate(x, n);
            }
            Item* new_items_group(){
                Item* x = item_allocator.allocate(ITEM_GROUP_SIZE);
                RT_ASSERT(x);
                return x;
            }
            
            std::allocator<bitmap_t> bitmap_allocator;
            bitmap_t* new_bitmap(int n){
                bitmap_t* x = bitmap_allocator.allocate(n);
                if(x!=nullptr){
                    return x;
                }
                std::cout<<"allocate failed"<<std::endl;
                return nullptr;
            }
            void delete_bitmap(bitmap_t* x, int n){
                bitmap_allocator.deallocate(x, n);
            }
                      
            std::allocator<slock> slock_allocator;
            slock* new_slock(int n){
                slock *x = slock_allocator.allocate(n);
                if(x!=nullptr){
                    return x;
                }
                std::cout<<"allocate failed"<<std::endl;
                return nullptr;
            }
            void delete_slock(slock* x,int n){
                slock_allocator.deallocate(x,n);
            }

            //--------------------------build tree---------------------------//
            
            //build empty subtree without key but range bound
            subtree* build_tree_none(K st,K ed){
                // subtree* n = new_subtree(1);
                subtree* n = new subtree(false,false,0,1);
                n->slope = n->intercept = 0;
                Item* item_set = new_items(1);
                memset(static_cast<void*>(item_set),0,sizeof(Item));
                n->matrixRow = 1;
                n->ItemMatrix = new_itemMatrix(1);
                n->ItemMatrix[0] = item_set;

                // n->items = new_items(1);
                // memset(n->items,0,sizeof(Item));
                n->mlock = new_slock(1);
                n->TryLockItem(0);
                n->ReleaseItem(0);
                n->none_bitmap = new_bitmap(1);
                n->none_bitmap[0] = 0;
                BITMAP_SET(n->none_bitmap, 0);
                n->child_bitmap = new_bitmap(1);
                n->child_bitmap[0] = 0;
                return n;
            }

            //build subtree without key but range bound
            subtree* build_tree_nokey(K start,K stop){
                RT_ASSERT(stop > start);
                const int slot_item = SLOT_INIT;
                subtree* n = new subtree(false,false,0,slot_item);
                int row_cnt = floor(n->num_items / ITEM_GROUP_SIZE);
                if(n->num_items % ((int)ITEM_GROUP_SIZE))
                    row_cnt++;
                if(row_cnt == 0)
                    row_cnt = 1;
                n->matrixRow = row_cnt;
                n->ItemMatrix = new_itemMatrix(row_cnt);
                this->CreateGroupKeyNumArray(row_cnt);
                this->CreateGroupDepth(row_cnt);
                int remain_slot = n->num_items;
                for(int i = 0;i<row_cnt;i++){
                    Item* item_set = nullptr;
                    if(remain_slot >= ITEM_GROUP_SIZE){
                        item_set = new_items_group();
                        memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                        remain_slot -= ITEM_GROUP_SIZE;
                    }else{
                        item_set = new_items(remain_slot);
                        memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                        remain_slot = 0;
                    }
                    n->ItemMatrix[i] = (item_set);
                    this->group_key_num[i] = 0;
                }
                // n->items = new_items(n->num_items);
                // memset(n->items,0,(n->num_items)*sizeof(Item));
                const int bitmap_size = BITMAP_SIZE(n->num_items);
                n->mlock = new_slock(bitmap_size);
                for(int i = 0;i<bitmap_size;i++){
                    n->TryLockItem(i*8);
                    n->ReleaseItem(i*8);
                }
                n->none_bitmap = new_bitmap(bitmap_size);
                n->child_bitmap = new_bitmap(bitmap_size);
                memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);
                // for(int i = 0;i<bitmap_size;i++){
                //     n->none_bitmap[i] = 0xff;
                //     n->child_bitmap[i] = 0;
                // }
                
                const long double mid1_key = (static_cast<long double>(stop) - static_cast<long double>(start))/3.0;
                const long double mid2_key = mid1_key*2;

                const long double mid1_target = n->num_items / 3;
                const long double mid2_target = n->num_items * 2 / 3;

                n->slope = (mid2_target - mid1_target) / (mid2_key - mid1_key);
                #if DEBUG_ASSERT
                RT_ASSERT(isinf(n->slope)==0);
                #endif
                n->intercept = mid1_target - n->slope * mid1_key;
                #if DEBUG_ASSERT
                RT_ASSERT(isfinite(n->slope));
                RT_ASSERT(isfinite(n->intercept));
                #endif
                return n;
            }

            //build subtree with model
            subtree* build_tree_two(K key1, V value1, K key2, V value2){
                if (key1 > key2) {
                    std::swap(key1, key2);
                    std::swap(value1, value2);
                }
                subtree* n = NULL;
                while(!CASPool()){;}
                if(tree_pool.empty()){
                    const int slot_item = 8;
                    n = new subtree(true,false,2,slot_item);
                    int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                    if(n->num_items % ((int)ITEM_GROUP_SIZE))
                        row_cnt++;
                    if(row_cnt == 0)
                        row_cnt = 1;
                    n->matrixRow = row_cnt;
                    n->ItemMatrix = new_itemMatrix(row_cnt);
                    int remain_slot = n->num_items;
                    for(int i = 0;i<row_cnt;i++){
                        Item* item_set = nullptr;
                        if(remain_slot >= ITEM_GROUP_SIZE){
                            item_set = new_items_group();
                            memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                            remain_slot -= ITEM_GROUP_SIZE;
                        }else{
                            item_set = new_items(remain_slot);
                            memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                            remain_slot = 0;
                        }
                        n->ItemMatrix[i] = (item_set);
                    }
                    // n->items = new_items(n->num_items);
                    // memset(n->items,0,(n->num_items)*sizeof(Item));
                    n->mlock = new_slock(1);
                    n->TryLockItem(0);
                    n->ReleaseItem(0);
                    n->none_bitmap = new_bitmap(1);
                    n->child_bitmap = new_bitmap(1);
                    n->none_bitmap[0] = 0xff;
                    n->child_bitmap[0] = 0;
                }else{
                    n = tree_pool.top();
                    n->ordered_array = false;
                    tree_pool.pop();
                }
                ReleasePool();
                
                const long double mid1_key = static_cast<long double>(key1);
                const long double mid2_key = static_cast<long double>(key2);

                const long double mid1_target = n->num_items / 3;
                const long double mid2_target = n->num_items * 2 / 3;

                n->slope = (mid2_target - mid1_target) / (mid2_key - mid1_key);
                #if DEBUG_ASSERT
                if(isinf(n->slope) != 0){
                    std::cout<<"???"<<std::endl;
                }
                // RT_ASSERT(isinf(n->slope)==0);
                #endif
                n->intercept = mid1_target - n->slope * mid1_key;
                #if DEBUG_ASSERT
                RT_ASSERT(isfinite(n->slope));
                RT_ASSERT(isfinite(n->intercept));
                #endif
                { // insert key1&value1
                    int pos = n->predict(key1);
                    #if DEBUG_ASSERT
                    RT_ASSERT(BITMAP_GET(n->none_bitmap, pos) == 1);
                    #endif
                    BITMAP_CLEAR(n->none_bitmap, pos);
                    Item it(key1,value1);
                    n->FillItemAt(pos,it);
                }
                { // insert key2&value2
                    int pos = n->predict(key2);
                    #if DEBUG_ASSERT
                    RT_ASSERT(BITMAP_GET(n->none_bitmap, pos) == 1);
                    #endif
                    BITMAP_CLEAR(n->none_bitmap, pos);
                    Item it(key2,value2);
                    n->FillItemAt(pos,it);
                }
                #if DEBUG_ASSERT
                RT_ASSERT(n!=NULL);
                #endif
                return n;
            }
     
            //build subtree without model
            subtree* build_tree_nomodel(K key1, V value1, K key2, V value2){
                //must be ordered
                if (key1 > key2) {
                    std::swap(key1, key2);
                    std::swap(value1, value2);
                }
                subtree* n = NULL;
                //数组需要有序
                const int item_slot = Threshold_Array;
                const int bitmap_size = BITMAP_SIZE(item_slot);
                n = new subtree(false,true,2,item_slot);
                int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                if(n->num_items % ((int)ITEM_GROUP_SIZE))
                    row_cnt++;
                if(row_cnt == 0)
                    row_cnt = 1;
                n->matrixRow = row_cnt;
                n->ItemMatrix = new_itemMatrix(row_cnt);
                int remain_slot = n->num_items;
                for(int i = 0;i<row_cnt;i++){
                    Item* item_set = nullptr;
                    if(remain_slot >= ITEM_GROUP_SIZE){
                        item_set = new_items_group();
                        memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                        remain_slot -= ITEM_GROUP_SIZE;
                    }else{
                        item_set = new_items(remain_slot);
                        memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                        remain_slot = 0;
                    }
                    n->ItemMatrix[i] = (item_set);
                }
                // n->items = new_items(n->num_items);
                // memset(n->items,0,(n->num_items)*sizeof(Item));
                n->mlock = new_slock(bitmap_size);
                for(int i = 0;i<bitmap_size;i++){
                    n->TryLockItem(i*8);
                    n->ReleaseItem(i*8);
                }
                
                n->none_bitmap = new_bitmap(bitmap_size);
                n->child_bitmap = new_bitmap(bitmap_size);
                memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);

                //为了简化，数组紧凑安排 //TODO: 优化
                //place key
                int pos;
                {
                    pos = 0;
                    BITMAP_CLEAR(n->none_bitmap, pos);
                    Item it(key1,value1);
                    n->FillItemAt(pos,it);
                }
                {
                    pos = 1;
                    BITMAP_CLEAR(n->none_bitmap, pos);
                    Item it(key2,value2);
                    n->FillItemAt(pos,it);
                }
                return n;
            }

            //build subtree without model
            subtree* build_tree_nomodel(K *_keys,V * _values,int ele_size){
                //keys must be ordered
                for(int i = 1;i<ele_size;i++){
                    if(_keys[i] <= _keys[i-1]){
                        cout<<"build_tree_nomodel error"<<endl;
                    }
                }
                subtree* n = NULL;
                //数组需要有序
                const int item_slot = Threshold_Array;
                const int bitmap_size = BITMAP_SIZE(item_slot);
                n = new subtree(false,true,ele_size,item_slot);
                int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                if(n->num_items % ((int)ITEM_GROUP_SIZE))
                    row_cnt++;
                if(row_cnt == 0)
                    row_cnt = 1;
                n->matrixRow = row_cnt;
                n->ItemMatrix = new_itemMatrix(row_cnt);
                int remain_slot = n->num_items;
                for(int i = 0;i<row_cnt;i++){
                    Item* item_set = nullptr;
                    if(remain_slot >= ITEM_GROUP_SIZE){
                        item_set = new_items_group();
                        memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                        remain_slot -= ITEM_GROUP_SIZE;
                    }else{
                        item_set = new_items(remain_slot);
                        memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                        remain_slot = 0;
                    }
                    n->ItemMatrix[i] = (item_set);
                }
                // n->items = new_items(n->num_items);
                // memset(n->items,0,(n->num_items)*sizeof(Item));
                n->mlock = new_slock(bitmap_size);
                for(int i = 0;i<bitmap_size;i++){
                    n->TryLockItem(i*8);
                    n->ReleaseItem(i*8);
                }
                
                n->none_bitmap = new_bitmap(bitmap_size);
                n->child_bitmap = new_bitmap(bitmap_size);
                memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);

                //为了简化，数组紧凑安排 //TODO: 优化
                //place key
                for(int i = 0;i<ele_size;i++){
                    BITMAP_CLEAR(n->none_bitmap, i);
                    n->FillItemAt(i,Item(_keys[i],_values[i]));
                    // n->items[i].comp.data = {_keys[i],_values[i]};
                }
                return n;
            }

            inline int compute_gap_count(int size) {
                if (size >= 1000000) return 1;
                if (size >= 100000) return 2;
                return 5;
            }
            
            //--------------------------write operation---------------------------//

            void insert_subtree(K key,V value,subtree** route_,int &path_size){
                subtree* n = DataArray;
                int pos = n->predict(key);
                StateType state_raw;
                // n->mlock->lock();
                n->LockItem(pos);
                state_raw = BITMAP_GET(n->none_bitmap, pos) == 1?0:BITMAP_GET(n->child_bitmap, pos)+1;
                // bool duplicate = false;
                while(1){
                    path_size++;
                    if(state_raw == ItemState::Empty){
                        BITMAP_CLEAR(n->none_bitmap, pos);
                        Item it(key,value);
                        n->FillItemAt(pos,it);
                        n->size.fetch_add(1, std::memory_order_acquire);
                        // n->mlock->unlock();
                        n->ReleaseItem(pos);
                        return;
                        // break;
                    }else if(state_raw == ItemState::Element){
                        Item it = n->GetItemAt(pos);
                        if(it.comp.data.key == key){
                            n->FillItemAt(pos,Item(key,value));
                            n->ReleaseItem(pos);
                            for(int i = 0;i<path_size-1;i++){
                                route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                            }
                            return;
                            // break;
                        }
                        subtree* next_subtree = nullptr;
                        // next_subtree = build_tree_two(key, value,n->items[pos].comp.data.key, 
                            // n->items[pos].comp.data.value);  
                        next_subtree = build_tree_nomodel(key, value,it.comp.data.key, 
                            it.comp.data.value);   
                        //replace
                        BITMAP_SET(n->child_bitmap, pos);
                        n->SetChildAt(pos,next_subtree);
                        n->size.fetch_add(1, std::memory_order_acquire);
                        // path_size++;
                        // n->mlock->unlock();
                        n->ReleaseItem(pos);
                        return;
                        // break;
                    }else{//ItemState::Subtree
                        n->size.fetch_add(1, std::memory_order_acquire);
                        RT_ASSERT(path_size < MAX_DEPTH*4 );
                        route_[path_size-1] = n;
                        subtree* next_n = n->GetItemAt(pos).comp.child;
                        if(next_n->ordered_array){
                            const int sub_node_size = next_n->size.load(std::memory_order_acquire);
                            if(sub_node_size < Threshold_Array){//directly insert
                                if(!( next_n->insert_array(sub_node_size,key,value) ) ){
                                    n->size.fetch_sub(1,std::memory_order_acquire);
                                    n->ReleaseItem(pos);
                                    for(int i = 0;i<path_size-1;i++){
                                        route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                                    }
                                    return;
                                }
                            }else{//rebuild
                                int small_pivot = next_n->BinarySearch(sub_node_size,key);
                                if(small_pivot>=0 && next_n->GetItemAt(small_pivot).comp.data.key == key){//重复的键
                                    n->size.fetch_sub(1,std::memory_order_acquire);
                                    n->ReleaseItem(pos);
                                    for(int i = 0;i<path_size-1;i++){
                                        route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                                    }
                                    return;
                                }
                                RT_ASSERT(small_pivot < 0 || next_n->GetItemAt(small_pivot).comp.data.key < key);
                                //rebuild with model
                                K *keys = new K[sub_node_size+1];
                                V *values = new V[sub_node_size+1];
                                for(int i = 0;i<=small_pivot;i++){
                                    keys[i] = next_n->GetItemAt(i).comp.data.key;
                                    values[i] = next_n->GetItemAt(i).comp.data.value;
                                }
                                keys[small_pivot+1] = key;
                                values[small_pivot+1] = value;
                                for(int i = small_pivot+1;i<sub_node_size;i++){
                                    keys[i+1] = next_n->GetItemAt(i).comp.data.key;
                                    values[i+1] = next_n->GetItemAt(i).comp.data.value;
                                }
                                subtree *new_sub = rebuild_tree_with_model(keys,values,sub_node_size+1).first;
                                n->SetChildAt(pos,new_sub);
                                //TODO DEBUG
                                // destroy_subtree(next_n);
                            }
                            n->ReleaseItem(pos);
                            return;
                        }
                        n->ReleaseItem(pos);
                        int next_pos = next_n->predict(key);
                        // next_n->mlock->lock();
                        next_n->LockItem(next_pos);
                        state_raw = BITMAP_GET(next_n->none_bitmap, next_pos) == 1?0:BITMAP_GET(next_n->child_bitmap, next_pos)+1;
                        n = next_n;
                        pos = next_pos;
                    }
                }
            }

            void insert_subtree_optimistic(K key,V value,subtree** route_,int &path_size,bool &worker_blocked,int &group_id){
                subtree* n = DataArray;
                int pos = n->predict(key);
                group_id = pos / ITEM_GROUP_SIZE;
                StateType state_raw;
                while(1){
                    path_size++;
                    //node does not support partial rebuild
                    //once node state = model,just go through
                    //otherwise, try to get lock then do insert
                    state_raw = BITMAP_GET(n->none_bitmap, pos) == 1?0:BITMAP_GET(n->child_bitmap, pos)+1;
                    // subtree *next = (*(n->items + pos)).comp.child;
                    subtree *next = n->GetItemAt(pos).comp.child;
                    
                    if(state_raw == ItemState::Subtree && next->ordered_array == false){
                        route_[path_size-1] = n;
                        n->size.fetch_add(1, std::memory_order_acquire);
                        n = n->GetItemAt(pos).comp.child;
                        pos = n->predict(key);
                        continue;
                    }
                    while(n->TryLockItem(pos) == false){
                        worker_blocked = true;
                    }
                    state_raw = BITMAP_GET(n->none_bitmap, pos) == 1?0:BITMAP_GET(n->child_bitmap, pos)+1;
                    if(state_raw == ItemState::Empty){
                        BITMAP_CLEAR(n->none_bitmap, pos);
                        n->FillItemAt(pos,Item(key,value));
                        n->size.fetch_add(1, std::memory_order_acquire);
                        n->ReleaseItem(pos);
                        return;
                    }
                    else if(state_raw == ItemState::Element){
                        Item it = n->GetItemAt(pos);
                        if(it.comp.data.key == key){
                            group_id = -1;
                            it.comp.data.value  = value;
                            n->FillItemAt(pos,it);
                            n->ReleaseItem(pos);
                            for(int i = 0;i<path_size-1;i++){
                                route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                            }
                            return;
                        }else{
                            subtree* next_subtree = build_tree_nomodel(key, value,it.comp.data.key, 
                                it.comp.data.value);   
                            n->SetChildAt(pos,next_subtree);
                            RT_ASSERT(n->ordered_array == false);
                            BITMAP_SET(n->child_bitmap, pos);
                            n->size.fetch_add(1, std::memory_order_acquire);
                            n->ReleaseItem(pos);
                            return;
                        }
                    }
                    else{//array or model
                        n->size.fetch_add(1, std::memory_order_acquire);
                        RT_ASSERT(path_size < MAX_DEPTH*4 );
                        route_[path_size-1] = n;
                        subtree* next_n = n->GetItemAt(pos).comp.child;
                        if(!(next_n->ordered_array)){
                            //next_n type swithc from array to model
                            n->ReleaseItem(pos);
                            pos = next_n->predict(key);
                            n = next_n;
                            continue;
                        }
                        const int sub_node_size = next_n->size.load(std::memory_order_acquire);
                        if(sub_node_size < Threshold_Array){//directly insert
                            if(next_n->insert_array(sub_node_size,key,value)){
                                n->ReleaseItem(pos);
                                return;
                            }
                            group_id = -1;
                            n->size.fetch_sub(1,std::memory_order_acquire);
                            n->ReleaseItem(pos);
                            for(int i = 0;i<path_size-1;i++){
                                route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                            }
                            return;  
                        }else{//rebuild
                            int small_pivot = next_n->BinarySearch(sub_node_size,key);
                            if(small_pivot>=0 && next_n->GetItemAt(small_pivot).comp.data.key == key){//重复的键
                                group_id = -1;
                                n->size.fetch_sub(1,std::memory_order_acquire);
                                n->ReleaseItem(pos);
                                for(int i = 0;i<path_size-1;i++){
                                    route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                                }
                                return;
                            }
                            RT_ASSERT(small_pivot < 0 || next_n->GetItemAt(small_pivot).comp.data.key < key);
                            //rebuild with model
                            K *keys = new K[sub_node_size+1];
                            V *values = new V[sub_node_size+1];
                            #if LeastSquaresTechniques
                            long long x_sum_ = key, y_sum_ = small_pivot+1;
                            long long xy_sum_ = (key*(small_pivot + 1)), xx_sum_ = (key * key);
                            #endif
                            for(int i = 0;i<=small_pivot;i++){
                                keys[i] = next_n->GetItemAt(i).comp.data.key;
                                values[i] = next_n->GetItemAt(i).comp.data.value;
                                #if LeastSquaresTechniques
                                x_sum_ += keys[i];
                                y_sum_ += i;
                                xy_sum_ += (keys[i] * i);
                                xx_sum_ += (keys[i] * keys[i]);
                                #endif
                            }
                            keys[small_pivot+1] = key;
                            values[small_pivot+1] = value;
                            for(int i = small_pivot+1;i<sub_node_size;i++){
                                keys[i+1] = next_n->GetItemAt(i).comp.data.key;
                                values[i+1] = next_n->GetItemAt(i).comp.data.value;
                                #if LeastSquaresTechniques
                                x_sum_ += keys[i];
                                y_sum_ += i;
                                xy_sum_ += (keys[i] * i);
                                xx_sum_ += (keys[i] * keys[i]);
                                #endif
                            }
                            RT_ASSERT(n->ordered_array == false);
                            #if LeastSquaresTechniques
                            long double slope = static_cast<long double>(
                                (static_cast<long double>(sub_node_size+1) * xy_sum_ - x_sum_ * y_sum_) /
                                (static_cast<long double>(sub_node_size+1) * xx_sum_ - x_sum_ * x_sum_));
                            long double intercept = static_cast<long double>(
                                (y_sum_ - static_cast<long double>(slope) * x_sum_) / (static_cast<double>(sub_node_size+1)));
                            subtree *next_subtree = rebuild_tree_FCMD(keys,values,slope,intercept,sub_node_size+1).first;
                            #else
                            subtree *next_subtree = rebuild_tree_FCMD(keys,values,sub_node_size+1).first;
                            #endif
                            // subtree *next_subtree = rebuild_tree_with_model(keys,values,sub_node_size+1).first;
                            n->SetChildAt(pos,next_subtree);
                            //TODO DEBUG
                            // destroy_subtree(next_n);
                            delete[] keys;
                            delete[] values;
                            n->ReleaseItem(pos);
                            return;
                        }
                    }
                }
            }

            bool Update(K key,V value){
                subtree* n = DataArray;
                int pos = n->predict(key);
                StateType state_raw;
                n->LockItem(pos);
                state_raw = BITMAP_GET(n->none_bitmap, pos) == 1?0:BITMAP_GET(n->child_bitmap, pos)+1;
                while(1){
                    Item it = n->GetItemAt(pos);
                    if(state_raw == ItemState::Empty){
                        return false;
                    }else if(state_raw == ItemState::Element){
                        if(it.comp.data.key == key){
                            it.comp.data.value = value;
                            n->FillItemAt(pos,it);
                            return true;
                        }
                        else{
                            return false;
                        }
                    }else{//ItemState::Subtree
                        subtree* next_n = it.comp.child;
                        if(next_n->ordered_array){
                            int sub_node_size = next_n->size.load(std::memory_order_acquire);
                            int small_pivot = next_n->BinarySearch(sub_node_size,key);
                            if(small_pivot>=0 && next_n->GetItemAt(small_pivot).comp.data.key == key){//重复的键
                                next_n->FillItemAt(small_pivot,Item(key,value));
                                n->ReleaseItem(pos);
                                return true;
                            }else{
                                n->ReleaseItem(pos);
                                return false;
                            }
                        }
                        n->ReleaseItem(pos);
                        int next_pos = next_n->predict(key);
                        next_n->LockItem(next_pos);
                        state_raw = BITMAP_GET(next_n->none_bitmap, next_pos) == 1?0:BITMAP_GET(next_n->child_bitmap, next_pos)+1;
                        n = next_n;
                        pos = next_pos;
                    }
                }
                return false;
            }

            bool Delete(K key,V value,subtree** route_){
                subtree* n = DataArray;
                int pos = n->predict(key);
                StateType state_raw;
                n->LockItem(pos);
                state_raw = BITMAP_GET(n->none_bitmap, pos) == 1?0:BITMAP_GET(n->child_bitmap, pos)+1;
                int path_size = 0;
                while(1){
                    route_[path_size] = n;
                    path_size++;
                    Item it = n->GetItemAt(pos);
                    if(state_raw == ItemState::Empty){
                        return false;
                    }else if(state_raw == ItemState::Element){
                        if(it.comp.data.key == key){
                            BITMAP_SET(n->none_bitmap,pos);
                            n->ReleaseItem(pos);
                            for(int i = 0;i<path_size;i++){
                                route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                            }
                            return true;
                        }
                        else{
                            n->ReleaseItem(pos);
                            return false;
                        }
                    }else{
                        subtree* next_n = it.comp.child;
                        if(next_n->ordered_array){
                            int sub_node_size = next_n->size.load(std::memory_order_acquire);
                            int small_pivot = next_n->BinarySearch(sub_node_size,key);
                            if(small_pivot>=0 && next_n->GetItemAt(small_pivot).comp.data.key == key){//重复的键
                                BITMAP_SET(next_n->none_bitmap,small_pivot);
                                next_n->size.fetch_sub(1,std::memory_order_acquire);
                                n->ReleaseItem(pos);
                                for(int i = 0;i<path_size;i++){
                                    route_[i]->size.fetch_sub(1,std::memory_order_acquire);
                                }
                                return true;
                            }else{
                                n->ReleaseItem(pos);
                                return false;
                            }
                        }
                        n->ReleaseItem(pos);
                        int next_pos = next_n->predict(key);
                        next_n->LockItem(next_pos);
                        state_raw = BITMAP_GET(next_n->none_bitmap, next_pos) == 1?0:BITMAP_GET(next_n->child_bitmap, next_pos)+1;
                        n = next_n;
                        pos = next_pos;
                    }
                }
                return false;
            }

            //--------------------------SMO operation---------------------------//

            void scan_and_destroy_subtree(subtree* root,K *keys,V *values,int ESIZE, bool destory = true){
                typedef std::pair<int, subtree*> Seg; // <begin, subtree*>
                std::stack<Seg> s;
                s.push(Seg(0, root));
                int key_cnt = 0;
                while (!s.empty()) {
                    int begin = s.top().first;
                    subtree* n = s.top().second;
                    s.pop();
                    for (int i = 0; i < n->num_items;i++) {
                        int none_byte = n->none_bitmap[i/BITMAP_WIDTH];
                        if(none_byte == 0xff){
                            i+=7;
                            continue;
                        }else if (((none_byte >> ((i) % BITMAP_WIDTH)) & 1) == 0) {
                            if (BITMAP_GET(n->child_bitmap, i) == 0) {
                                keys[begin] = n->GetItemAt(i).comp.data.key;
                                values[begin] = n->GetItemAt(i).comp.data.value;
                                begin ++;
                                key_cnt++;
                            } else {
                                Seg next_seg;
                                next_seg.first = begin;
                                next_seg.second = n->GetItemAt(i).comp.child;
                                s.push(next_seg);
                                begin += n->GetItemAt(i).comp.child->size.load(std::memory_order_acquire);
                            }
                        }
                    }
                    if (destory) {
                        if(n->is_two){
                            n->size.store(2, std::memory_order_release);
                            n->num_items = 8;
                            n->ordered_array = false;
                            memset(static_cast<void*>(n->ItemMatrix[0]),0,n->num_items*sizeof(Item));
                            // memset(n->items,0,(n->num_items)*sizeof(Item));
                            n->none_bitmap[0] = 0xff;
                            n->child_bitmap[0] = 0;
                            n->TryLockItem(0);
                            n->ReleaseItem(0);
                            while(!CASPool()){;}
                            tree_pool.push(n);
                            ReleasePool();
                        }else{
                            int slot_num = n->num_items;
                            for(int items_i = 0;items_i<n->matrixRow;items_i++){
                                Item *items_ = n->ItemMatrix[items_i];
                                if(items_i < n->matrixRow-1){
                                    delete_items(items_,ITEM_GROUP_SIZE);
                                    slot_num-=ITEM_GROUP_SIZE;
                                }   
                                else{
                                    delete_items(items_,slot_num);
                                }
                            }
                            delete_itemsMatrix(n->ItemMatrix,n->matrixRow);
                            // delete_items(n->items, n->num_items);
                            const int bitmap_size = BITMAP_SIZE(n->num_items);
                            delete_bitmap(n->none_bitmap, bitmap_size);
                            delete_bitmap(n->child_bitmap, bitmap_size);
                            delete_slock(n->mlock,bitmap_size);
                            delete_subtree(n, 1);
                        }
                    }
                }
                RT_ASSERT(key_cnt == ESIZE);
            }

            //least squares techniques build model
            void scan_and_destroy_subtree(subtree* root,K *keys,V *values,int ESIZE,M &slope,M &intercept, bool destory = true){
                typedef std::pair<int, subtree*> Seg; // <begin, subtree*>
                std::stack<Seg> s;
                s.push(Seg(0, root));
                int key_cnt = 0;
                long double x_sum_ = 0,y_sum_ = 0;
                long double xx_sum_ = 0,xy_sum_ = 0;

                while (!s.empty()) {
                    int begin = s.top().first;
                    subtree* n = s.top().second;
                    s.pop();
                    for (int i = 0; i < n->num_items;i++) {
                        int none_byte = n->none_bitmap[i/BITMAP_WIDTH];
                        if(none_byte == 0xff){
                            i+=7;
                            continue;
                        }else if (((none_byte >> ((i) % BITMAP_WIDTH)) & 1) == 0) {
                            if (BITMAP_GET(n->child_bitmap, i) == 0) {
                                keys[begin] = n->GetItemAt(i).comp.data.key;
                                values[begin] = n->GetItemAt(i).comp.data.value;
                                x_sum_ += keys[begin];
                                y_sum_ += key_cnt;
                                xy_sum_ += (keys[begin] * key_cnt);
                                xx_sum_ += (keys[begin] * keys[begin]);
                                begin ++;
                                key_cnt++;
                            } else {
                                Seg next_seg;
                                next_seg.first = begin;
                                next_seg.second = n->GetItemAt(i).comp.child;
                                s.push(next_seg);
                                begin += n->GetItemAt(i).comp.child->size.load(std::memory_order_acquire);
                            }
                        }
                    }
                    if (destory) {
                        if(n->is_two){
                            n->size.store(2, std::memory_order_release);
                            n->num_items = 8;
                            n->ordered_array = false;
                            memset(static_cast<void*>(n->ItemMatrix[0]),0,n->num_items*sizeof(Item));
                            // memset(n->items,0,(n->num_items)*sizeof(Item));
                            n->none_bitmap[0] = 0xff;
                            n->child_bitmap[0] = 0;
                            n->TryLockItem(0);
                            n->ReleaseItem(0);
                            while(!CASPool()){;}
                            tree_pool.push(n);
                            ReleasePool();
                        }else{
                            int slot_num = n->num_items;
                            for(int items_i = 0;items_i<n->matrixRow;items_i++){
                                Item *items_ = n->ItemMatrix[items_i];
                                if(items_i < n->matrixRow-1){
                                    delete_items(items_,ITEM_GROUP_SIZE);
                                    slot_num-=ITEM_GROUP_SIZE;
                                }   
                                else{
                                    delete_items(items_,slot_num);
                                }
                            }
                            delete_itemsMatrix(n->ItemMatrix,n->matrixRow);
                            // delete_items(n->items, n->num_items);
                            const int bitmap_size = BITMAP_SIZE(n->num_items);
                            delete_bitmap(n->none_bitmap, bitmap_size);
                            delete_bitmap(n->child_bitmap, bitmap_size);
                            delete_slock(n->mlock,bitmap_size);
                            delete_subtree(n, 1);
                        }
                    }
                }
                RT_ASSERT(key_cnt == ESIZE);
                slope = static_cast<double>(
                    (static_cast<long double>(key_cnt) * xy_sum_ - x_sum_ * y_sum_) /
                    (static_cast<long double>(key_cnt) * xx_sum_ - x_sum_ * x_sum_));
                intercept = static_cast<double>(
                    (y_sum_ - static_cast<long double>(slope) * x_sum_) / key_cnt);
            }

            std::pair<subtree*,int> rebuild_tree_with_model(K *_keys,V * _values,int _size){
                RT_ASSERT(_size > 1);
                typedef struct {
                        int begin;
                        int end;
                        int lvl; // top lvl = 1
                        subtree* n;
                } Seg;
                std::queue<Seg> s;
                subtree *ret = new subtree(_size == 2,false,_size);
                s.push({0, _size, 1, ret});
                int max_depth = 0;
                while(!s.empty()){
                    const int begin = s.front().begin;
                    const int end = s.front().end;
                    const int lvl = s.front().lvl;
                    max_depth = max(max_depth,lvl);
                    subtree* n = s.front().n;
                    s.pop();
                    #if DEBUG_ASSERT
                    RT_ASSERT(end - begin >= 2);
                    #endif
                    if(end-begin == 2){
                        //start and stop are set up in advance
                        subtree* _ = build_tree_two(_keys[begin], _values[begin], _keys[begin+1], _values[begin+1]);
                        memcpy(n,_,sizeof(subtree));//shalow copy
                        delete _;
                        // delete_subtree(_, 1);
                        if(lvl == 1){
                            ret = n;
                        }
                    }
                    else{
                        K * keys = _keys + begin;
                        V * values = _values + begin;
                        const int size = end - begin;
                        const int BUILD_GAP_CNT = compute_gap_count(size);
                        
                        //Get model
                        {
                            const int fourth_interval = (size - 1) / 4;
                            int mid1_pos,mid2_pos;
                            if(begin == 0){
                                mid1_pos = (size - 1) / 3 ;
                            }else{
                                mid1_pos = fourth_interval ;
                            }
                            mid1_pos = (max(0,mid1_pos-1)) % (size-2);
                            mid2_pos = min(size-2,(fourth_interval* 3  + 1));
                            #if DEBUG_ASSERT
                            if(mid1_pos >= mid2_pos){
                                cout<<mid1_pos<<"\t"<<mid2_pos<<endl;
                            }
                            RT_ASSERT(0 <= mid1_pos);
                            RT_ASSERT(mid1_pos < mid2_pos);
                            RT_ASSERT(mid2_pos < size - 1);
                            #endif
                            const long double mid1_key =
                                    (static_cast<long double>(keys[mid1_pos]) + static_cast<long double>(keys[min(size - 1,mid1_pos + 1)]) ) / 2;
                            const long double mid2_key =
                                    (static_cast<long double>(keys[mid2_pos]) + static_cast<long double>(keys[min(size - 1,mid2_pos + 1)]) ) / 2;

                            n->num_items = size * static_cast<int>(BUILD_GAP_CNT + 1);
                            
                            const long double mid1_target = mid1_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;
                            const long double mid2_target = mid2_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;
                            #if DEBUG_ASSERT
                            RT_ASSERT(abs(mid2_key - mid1_key)>1e-8);
                            #endif
                            n->slope = (mid2_target - mid1_target) / (mid2_key - mid1_key);
                            n->intercept = mid1_target - n->slope * mid1_key;
                            #if DEBUG_ASSERT
                            RT_ASSERT(isfinite(n->slope));
                            RT_ASSERT(isfinite(n->intercept));
                            #endif
                            
                        }
                        int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                        if(n->num_items % ((int)ITEM_GROUP_SIZE))
                            row_cnt++;
                        if(row_cnt == 0)
                            row_cnt = 1;
                        n->matrixRow = row_cnt;
                        n->ItemMatrix = new_itemMatrix(row_cnt);
                        int remain_slot = n->num_items;
                        for(int i = 0;i<row_cnt;i++){
                            Item* item_set = nullptr;
                            if(remain_slot >= ITEM_GROUP_SIZE){
                                item_set = new_items_group();
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                                remain_slot -= ITEM_GROUP_SIZE;
                            }else{
                                item_set = new_items(remain_slot);
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                                remain_slot = 0;
                            }
                            n->ItemMatrix[i] = (item_set);
                        }     
                        // n->items = new_items(n->num_items);
                        // memset(n->items,0,n->num_items*sizeof(Item));
                        
                        const int bitmap_size = BITMAP_SIZE(n->num_items);
                        n->mlock = new_slock(bitmap_size);
                        for(int i = 0;i<bitmap_size;i++){
                            n->TryLockItem(i*8);
                            n->ReleaseItem(i*8);
                        }
                        n->none_bitmap = new_bitmap(bitmap_size);
                        n->child_bitmap = new_bitmap(bitmap_size);
                        memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                        memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);
                        
                        //re-insert
                        int item_i = n->predict(keys[0]);
                        for (int offset = 0; offset < size; ) {
                            int next = offset + 1, next_i = -1;
                            while (next < size) {     
                                next_i = n->predict( keys[next]);
                                if (next_i == item_i) {
                                    next ++;
                                } else {
                                    break;
                                }
                            }
                            #if DEBUG_ASSERT
                            RT_ASSERT(item_i < n->num_items);
                            #endif
                            if (next == offset + 1) {
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                n->FillItemAt(item_i,Item(keys[offset],values[offset]));
                                // n->items[item_i].comp.data.key = keys[offset];
                                // n->items[item_i].comp.data.value = values[offset];
                            } else {
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                //TODO DEBUG
                                RT_ASSERT(n->ordered_array == false);
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                BITMAP_SET(n->child_bitmap, item_i);
                                subtree *_ = new subtree(next-offset == 2,false,next-offset);
                                n->SetChildAt(item_i,_);
                                // n->items[item_i].comp.child = _;
                                s.push({begin + offset, begin + next, lvl + 1, _});
                            }
                            if (next >= size) {
                                break;
                            } else {
                                item_i = next_i;
                                offset = next;
                            }
                        }
                    }   
                }
                return {ret,max_depth};
            }

            //对于<Threshold_Array个key冲突产生的非top的subtree不使用model
            std::pair<subtree*,int> rebuild_tree(K *_keys,V * _values,int _size,bool plr = false,M top_slope = 0,M top_intercept = 0){
                //plr means whether to use the model from plr
                //top_slope , top_intercept are the model from the plr
                RT_ASSERT(_size > 1);
                typedef struct {
                        int begin;
                        int end;
                        int lvl; // top lvl = 1
                        subtree* n;
                } Seg;
                std::queue<Seg> s;
                subtree *ret = new subtree(_size == 2,false,_size);
                // subtree* ret = new_subtree(1);
                s.push({0, _size, 1, ret});
                int max_depth = 0;
                while(!s.empty()){
                    const int begin = s.front().begin;
                    const int end = s.front().end;
                    const int lvl = s.front().lvl;
                    max_depth = max(max_depth,lvl);
                    subtree* n = s.front().n;
                    s.pop();
                    #if DEBUG_ASSERT
                    RT_ASSERT(end - begin >= 2);
                    #endif
                    if(end - begin < Threshold_Array  && lvl >1){
                        subtree* _ = build_tree_nomodel(_keys+begin, _values+begin, end-begin);
                        memcpy(n, _, sizeof(subtree));//shalow copy
                        delete _;
                        continue;
                    }
                    //end - begin > threshold || lvl == 1 
                    if(lvl == 1 && end - begin == 2){
                        subtree* _ = build_tree_two(_keys[begin], _values[begin], _keys[begin+1], _values[begin+1]);
                        memcpy(n,_,sizeof(subtree));
                        delete _;
                        ret = n;
                        continue;
                    }
                    //end - begin > threshold || lvl == 1
                    {
                        RT_ASSERT(n->ordered_array == false);
                        K * keys = _keys + begin;
                        V * values = _values + begin;
                        const int size = end - begin;
                        const int BUILD_GAP_CNT = compute_gap_count(size);
                        n->is_two = 0;
                        n->size.store(size, std::memory_order_release);
                        if(plr && lvl == 1){
                            n->num_items = size;
                            n->slope = top_slope;
                            n->intercept = top_intercept;
                            #if DEBUG_ASSERT
                            RT_ASSERT(isfinite(n->slope));
                            RT_ASSERT(isfinite(n->intercept));
                            #endif
                        }
                        else{
                            const int fourth_interval = (size - 1) / 4;
                            int mid1_pos,mid2_pos;
                            if(begin == 0){
                                mid1_pos = (size - 1) / 3 ;
                            }else{
                                // int random_scale = rand()%10;//不要用rand
                                mid1_pos = fourth_interval ;// * random_scale / 10;
                            }
                            mid1_pos = (max(0,mid1_pos-1)) % (size-2);
                            // int random_scale = rand()%10;
                            mid2_pos = min(size-2,(fourth_interval* 3  + 1));//+ fourth_interval * random_scale / 10
                            #if DEBUG_ASSERT
                            if(mid1_pos >= mid2_pos){
                                cout<<mid1_pos<<"\t"<<mid2_pos<<endl;
                            }
                            RT_ASSERT(0 <= mid1_pos);
                            RT_ASSERT(mid1_pos < mid2_pos);
                            RT_ASSERT(mid2_pos < size - 1);
                            #endif
                            const long double mid1_key =
                                    (static_cast<long double>(keys[mid1_pos]) + static_cast<long double>(keys[min(size - 1,mid1_pos + 1)]) ) / 2;
                            const long double mid2_key =
                                    (static_cast<long double>(keys[mid2_pos]) + static_cast<long double>(keys[min(size - 1,mid2_pos + 1)]) ) / 2;
                            
                            n->num_items = size * static_cast<int>(BUILD_GAP_CNT + 1);
                            
                            const long double mid1_target = mid1_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;
                            const long double mid2_target = mid2_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;
                            #if DEBUG_ASSERT
                            RT_ASSERT(abs(mid2_key - mid1_key)>1e-8);
                            #endif
                            n->slope = (mid2_target - mid1_target) / (mid2_key - mid1_key);
                            n->intercept = mid1_target - n->slope * mid1_key;
                            #if DEBUG_ASSERT
                            RT_ASSERT(isfinite(n->slope));
                            RT_ASSERT(isfinite(n->intercept));
                            #endif
                        }        
                        #if DEBUG_ASSERT
                        RT_ASSERT(n->slope >= 0);
                        #endif
                        int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                        if(n->num_items % ((int)ITEM_GROUP_SIZE))
                            row_cnt++;
                        if(row_cnt == 0)
                            row_cnt = 1;
                        n->matrixRow = row_cnt;
                        n->ItemMatrix = new_itemMatrix(row_cnt);
                        int remain_slot = n->num_items;
                        for(int i = 0;i<row_cnt;i++){
                            Item* item_set = nullptr;
                            if(remain_slot >= ITEM_GROUP_SIZE){
                                item_set = new_items_group();
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                                remain_slot -= ITEM_GROUP_SIZE;
                            }else{
                                item_set = new_items(remain_slot);
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                                remain_slot = 0;
                            }
                            n->ItemMatrix[i] = (item_set);
                        }
                        // n->items = new_items(n->num_items);
                        // memset(n->items,0,n->num_items*sizeof(Item));
                        
                        const int bitmap_size = BITMAP_SIZE(n->num_items);
                        n->mlock = new_slock(bitmap_size);
                        for(int i = 0;i<bitmap_size;i++){
                            n->TryLockItem(i*8);
                            n->ReleaseItem(i*8);
                        }
                        n->none_bitmap = new_bitmap(bitmap_size);
                        n->child_bitmap = new_bitmap(bitmap_size);
                        memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                        memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);
                        int item_i = n->predict(keys[0]);
                        for (int offset = 0; offset < size; ) {
                            int next = offset + 1, next_i = -1;
                            while (next < size) {  
                                #if DEBUG   
                                if(keys[next] <= keys[next-1]){
                                    cout<<"key unordered"<<endl;
                                }
                                #endif
                                next_i = n->predict( keys[next]);
                                if (next_i == item_i) {
                                    next ++;
                                } else {
                                    break;
                                }
                            }
                            #if DEBUG_ASSERT
                            RT_ASSERT(item_i < n->num_items);
                            #endif
                            if (next == offset + 1) {
                                if(BITMAP_GET(n->none_bitmap,item_i) == 0){
                                    cout<<"bitmap error"<<endl;
                                }
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                Item it_local(keys[offset],values[offset]);
                                n->ItemMatrix[item_i / ITEM_GROUP_SIZE][item_i % ITEM_GROUP_SIZE] = it_local;
                                // n->FillItemAt(item_i,it_local);
                                // n->items[item_i].comp.data.key = keys[offset];
                                // n->items[item_i].comp.data.value = values[offset];
                            } else {
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                BITMAP_SET(n->child_bitmap, item_i);
                                if(next - offset < Threshold_Array){
                                    n->SetChildAt(item_i,build_tree_nomodel(keys+offset, values+offset, next-offset));
                                    // n->items[item_i].comp.child = build_tree_nomodel(keys+offset, values+offset, next-offset);
                                    // n->items[item_i].comp.child = new subtree(false,true,next-offset,Threshold_Array);
                                }else{
                                    subtree *child_n = new subtree(false,false,next-offset);
                                    n->SetChildAt(item_i,child_n);
                                    // n->items[item_i].comp.child = new subtree(false,false,next-offset);
                                    s.push({begin + offset, begin + next, lvl + 1, child_n});
                                }                                
                            }
                            if (next >= size) {
                                break;
                            } else {
                                item_i = next_i;
                                offset = next;
                            }
                        }
                    }   
                }
                return {ret,max_depth};
            }

            std::pair<subtree*,int> rebuild_tree_FCMD(K *_keys,V * _values,int _size,vector<int>&after_smo_group_key){
                //plr means whether to use the model from plr
                //top_slope , top_intercept are the model from the plr
                RT_ASSERT(_size > 1);
                typedef struct {
                        int begin;
                        int end;
                        int lvl; // top lvl = 1
                        subtree* n;
                } Seg;
                std::queue<Seg> s;
                subtree *ret = new subtree(_size == 2,false,_size);
                // subtree* ret = new_subtree(1);
                s.push({0, _size, 1, ret});
                int max_depth = 0;
                while(!s.empty()){
                    const int begin = s.front().begin;
                    const int end = s.front().end;
                    const int lvl = s.front().lvl;
                    max_depth = max(max_depth,lvl);
                    subtree* n = s.front().n;
                    s.pop();
                    #if DEBUG_ASSERT
                    RT_ASSERT(end - begin >= 2);
                    #endif
                    if(end - begin < Threshold_Array  && lvl >1){
                        subtree* _ = build_tree_nomodel(_keys+begin, _values+begin, end-begin);
                        memcpy(n, _, sizeof(subtree));//shalow copy
                        delete _;
                        continue;
                    }
                    if(lvl == 1 && end - begin == 2){
                        subtree* _ = build_tree_two(_keys[begin], _values[begin], _keys[begin+1], _values[begin+1]);
                        memcpy(n,_,sizeof(subtree));
                        delete _;
                        ret = n;
                        after_smo_group_key.resize(1);
                        after_smo_group_key[0] = 2;
                        continue;
                    }
                    //end - begin > threshold || lvl == 1
                    {
                        RT_ASSERT(n->ordered_array == false);
                        K * keys = _keys + begin;
                        V * values = _values + begin;
                        const int size = end - begin;
                        const int BUILD_GAP_CNT = compute_gap_count(size);
                        n->is_two = 0;
                        n->size.store(size, std::memory_order_release);
                        {//fmcd
                            const int L = size * static_cast<int>(BUILD_GAP_CNT + 1);
                            int i = 0;
                            int D = 1;
                            RT_ASSERT(D <= size-1-D);
                            double Ut = (static_cast<long double>(keys[size - 1 - D]) - static_cast<long double>(keys[D])) /
                                        (static_cast<double>(L - 2)) + 1e-6;
                            while (i < size - 1 -D){
                                while (i + D < size && keys[i + D] - keys[i] >= Ut) {
                                    i ++;
                                }
                                if(i + D >= size){
                                    break;
                                }
                                D = D + 1;
                                if (D * 3 > size) break;
                                RT_ASSERT(D <= size-1-D);
                                Ut = (static_cast<long double>(keys[size - 1 - D]) - static_cast<long double>(keys[D])) /
                                    (static_cast<double>(L - 2)) + 1e-6;
                            }
                            if (D * 3 <= size) {
                                n->slope = 1.0 / Ut;
                                n->intercept = (L - n->slope * (static_cast<long double>(keys[size - 1 - D]) +
                                                                    static_cast<long double>(keys[D]))) / 2;
                                RT_ASSERT(isfinite(n->slope));
                                RT_ASSERT(isfinite(n->intercept));
                                n->num_items = L;
                            }else{
                                
                                int mid1_pos = (size - 1) / 3;
                                int mid2_pos = (size - 1) * 2 / 3;

                                RT_ASSERT(0 <= mid1_pos);
                                RT_ASSERT(mid1_pos < mid2_pos);
                                RT_ASSERT(mid2_pos < size - 1);

                                const long double mid1_key = (static_cast<long double>(keys[mid1_pos]) +
                                                            static_cast<long double>(keys[mid1_pos + 1])) / 2;
                                const long double mid2_key = (static_cast<long double>(keys[mid2_pos]) +
                                                            static_cast<long double>(keys[mid2_pos + 1])) / 2;

                                n->num_items = size * static_cast<int>(BUILD_GAP_CNT + 1);
                                const double mid1_target = mid1_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;
                                const double mid2_target = mid2_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;

                                n->slope = (mid2_target - mid1_target) / (mid2_key - mid1_key);
                                n->intercept = mid1_target - n->slope * mid1_key;
                                RT_ASSERT(isfinite(n->slope));
                                RT_ASSERT(isfinite(n->intercept));
                            }
                            
                        }        
                        #if DEBUG_ASSERT
                        RT_ASSERT(n->slope >= 0);
                        #endif
                        
                        int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                        if(n->num_items % ((int)ITEM_GROUP_SIZE))
                            row_cnt++;
                        if(row_cnt == 0)
                            row_cnt = 1;
                        n->matrixRow = row_cnt;
                        n->ItemMatrix = new_itemMatrix(row_cnt);
                        if(lvl == 1){
                            after_smo_group_key.resize(row_cnt);
                            for(int g = 0;g<row_cnt;g++){
                                after_smo_group_key[g] = 0;
                            }
                        }
                        int remain_slot = n->num_items;
                        for(int i = 0;i<row_cnt;i++){
                            Item* item_set = nullptr;
                            if(remain_slot >= ITEM_GROUP_SIZE){
                                item_set = new_items_group();
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                                remain_slot -= ITEM_GROUP_SIZE;
                            }else{
                                item_set = new_items(remain_slot);
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                                remain_slot = 0;
                            }
                            n->ItemMatrix[i] = (item_set);
                        }
                        // n->items = new_items(n->num_items);
                        // memset(n->items,0,n->num_items*sizeof(Item));
                        
                        const int bitmap_size = BITMAP_SIZE(n->num_items);
                        n->mlock = new_slock(bitmap_size);
                        for(int i = 0;i<bitmap_size;i++){
                            n->TryLockItem(i*8);
                            n->ReleaseItem(i*8);
                        }
                        n->none_bitmap = new_bitmap(bitmap_size);
                        n->child_bitmap = new_bitmap(bitmap_size);
                        memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                        memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);
                        int item_i = n->predict(keys[0]);
                        for (int offset = 0; offset < size; ) {
                            int next = offset + 1, next_i = -1;
                            while (next < size) {  
                                #if DEBUG   
                                if(keys[next] <= keys[next-1]){
                                    cout<<"key unordered"<<endl;
                                }
                                #endif
                                next_i = n->predict( keys[next]);
                                if (next_i == item_i) {
                                    next ++;
                                } else {
                                    break;
                                }
                            }
                            #if DEBUG_ASSERT
                            RT_ASSERT(item_i < n->num_items);
                            #endif
                            if (next == offset + 1) {
                                if(BITMAP_GET(n->none_bitmap,item_i) == 0){
                                    cout<<"bitmap error"<<endl;
                                }
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                Item it_local(keys[offset],values[offset]);
                                n->ItemMatrix[item_i / ITEM_GROUP_SIZE][item_i % ITEM_GROUP_SIZE] = it_local;
                                if(lvl == 1){
                                    after_smo_group_key[item_i / ITEM_GROUP_SIZE]++;
                                }
                                // n->FillItemAt(item_i,it_local);
                                // n->items[item_i].comp.data.key = keys[offset];
                                // n->items[item_i].comp.data.value = values[offset];
                            } else {
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                BITMAP_SET(n->child_bitmap, item_i);
                                if(lvl == 1){
                                    after_smo_group_key[item_i / ITEM_GROUP_SIZE]+=(next - offset);
                                }
                                if(next - offset < Threshold_Array){
                                    n->SetChildAt(item_i,build_tree_nomodel(keys+offset, values+offset, next-offset));
                                    // n->items[item_i].comp.child = build_tree_nomodel(keys+offset, values+offset, next-offset);
                                    // n->items[item_i].comp.child = new subtree(false,true,next-offset,Threshold_Array);
                                }else{
                                    subtree *child_n = new subtree(false,false,next-offset);
                                    n->SetChildAt(item_i,child_n);
                                    // n->items[item_i].comp.child = new subtree(false,false,next-offset);
                                    s.push({begin + offset, begin + next, lvl + 1, child_n});
                                }                                
                            }
                            if (next >= size) {
                                break;
                            } else {
                                item_i = next_i;
                                offset = next;
                            }
                        }
                    }   
                }
                return {ret,max_depth};
            }

            std::pair<subtree*,int> rebuild_tree_FCMD(K *_keys,V * _values,int _size){
                //plr means whether to use the model from plr
                //top_slope , top_intercept are the model from the plr
                RT_ASSERT(_size > 1);
                typedef struct {
                        int begin;
                        int end;
                        int lvl; // top lvl = 1
                        subtree* n;
                } Seg;
                std::queue<Seg> s;
                subtree *ret = new subtree(_size == 2,false,_size);
                // subtree* ret = new_subtree(1);
                s.push({0, _size, 1, ret});
                int max_depth = 0;
                while(!s.empty()){
                    const int begin = s.front().begin;
                    const int end = s.front().end;
                    const int lvl = s.front().lvl;
                    max_depth = max(max_depth,lvl);
                    subtree* n = s.front().n;
                    s.pop();
                    #if DEBUG_ASSERT
                    RT_ASSERT(end - begin >= 2);
                    #endif
                    if(end - begin < Threshold_Array  && lvl >1){
                        subtree* _ = build_tree_nomodel(_keys+begin, _values+begin, end-begin);
                        memcpy(n, _, sizeof(subtree));//shalow copy
                        delete _;
                        continue;
                    }
                    if(lvl == 1 && end - begin == 2){
                        subtree* _ = build_tree_two(_keys[begin], _values[begin], _keys[begin+1], _values[begin+1]);
                        memcpy(n,_,sizeof(subtree));
                        delete _;
                        ret = n;
                        continue;
                    }
                    //end - begin > threshold || lvl == 1
                    {
                        RT_ASSERT(n->ordered_array == false);
                        K * keys = _keys + begin;
                        V * values = _values + begin;
                        const int size = end - begin;
                        const int BUILD_GAP_CNT = compute_gap_count(size);
                        n->is_two = 0;
                        n->size.store(size, std::memory_order_release);
                        {//fmcd
                            const int L = size * static_cast<int>(BUILD_GAP_CNT + 1);
                            int i = 0;
                            int D = 1;
                            RT_ASSERT(D <= size-1-D);
                            double Ut = (static_cast<long double>(keys[size - 1 - D]) - static_cast<long double>(keys[D])) /
                                        (static_cast<double>(L - 2)) + 1e-6;
                            while (i < size - 1 -D){
                                while (i + D < size && keys[i + D] - keys[i] >= Ut) {
                                    i ++;
                                }
                                if(i + D >= size){
                                    break;
                                }
                                D = D + 1;
                                if (D * 3 > size) break;
                                RT_ASSERT(D <= size-1-D);
                                Ut = (static_cast<long double>(keys[size - 1 - D]) - static_cast<long double>(keys[D])) /
                                    (static_cast<double>(L - 2)) + 1e-6;
                            }
                            if (D * 3 <= size) {
                                n->slope = 1.0 / Ut;
                                n->intercept = (L - n->slope * (static_cast<long double>(keys[size - 1 - D]) +
                                                                    static_cast<long double>(keys[D]))) / 2;
                                RT_ASSERT(isfinite(n->slope));
                                RT_ASSERT(isfinite(n->intercept));
                                n->num_items = L;
                            }else{
                                
                                int mid1_pos = (size - 1) / 3;
                                int mid2_pos = (size - 1) * 2 / 3;

                                RT_ASSERT(0 <= mid1_pos);
                                RT_ASSERT(mid1_pos < mid2_pos);
                                RT_ASSERT(mid2_pos < size - 1);

                                const long double mid1_key = (static_cast<long double>(keys[mid1_pos]) +
                                                            static_cast<long double>(keys[mid1_pos + 1])) / 2;
                                const long double mid2_key = (static_cast<long double>(keys[mid2_pos]) +
                                                            static_cast<long double>(keys[mid2_pos + 1])) / 2;

                                n->num_items = size * static_cast<int>(BUILD_GAP_CNT + 1);
                                const double mid1_target = mid1_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;
                                const double mid2_target = mid2_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;

                                n->slope = (mid2_target - mid1_target) / (mid2_key - mid1_key);
                                n->intercept = mid1_target - n->slope * mid1_key;
                                RT_ASSERT(isfinite(n->slope));
                                RT_ASSERT(isfinite(n->intercept));
                            }
                            
                        }        
                        #if DEBUG_ASSERT
                        RT_ASSERT(n->slope >= 0);
                        #endif
                        
                        int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                        if(n->num_items % ((int)ITEM_GROUP_SIZE))
                            row_cnt++;
                        if(row_cnt == 0)
                            row_cnt = 1;
                        n->matrixRow = row_cnt;
                        n->ItemMatrix = new_itemMatrix(row_cnt);
                        
                        int remain_slot = n->num_items;
                        for(int i = 0;i<row_cnt;i++){
                            Item* item_set = nullptr;
                            if(remain_slot >= ITEM_GROUP_SIZE){
                                item_set = new_items_group();
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                                remain_slot -= ITEM_GROUP_SIZE;
                            }else{
                                item_set = new_items(remain_slot);
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                                remain_slot = 0;
                            }
                            n->ItemMatrix[i] = (item_set);
                        }
                        // n->items = new_items(n->num_items);
                        // memset(n->items,0,n->num_items*sizeof(Item));
                        
                        const int bitmap_size = BITMAP_SIZE(n->num_items);
                        n->mlock = new_slock(bitmap_size);
                        for(int i = 0;i<bitmap_size;i++){
                            n->TryLockItem(i*8);
                            n->ReleaseItem(i*8);
                        }
                        n->none_bitmap = new_bitmap(bitmap_size);
                        n->child_bitmap = new_bitmap(bitmap_size);
                        memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                        memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);
                        int item_i = n->predict(keys[0]);
                        for (int offset = 0; offset < size; ) {
                            int next = offset + 1, next_i = -1;
                            while (next < size) {  
                                #if DEBUG   
                                if(keys[next] <= keys[next-1]){
                                    cout<<"key unordered"<<endl;
                                }
                                #endif
                                next_i = n->predict( keys[next]);
                                if (next_i == item_i) {
                                    next ++;
                                } else {
                                    break;
                                }
                            }
                            #if DEBUG_ASSERT
                            RT_ASSERT(item_i < n->num_items);
                            #endif
                            if (next == offset + 1) {
                                if(BITMAP_GET(n->none_bitmap,item_i) == 0){
                                    cout<<"bitmap error"<<endl;
                                }
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                Item it_local(keys[offset],values[offset]);
                                n->ItemMatrix[item_i / ITEM_GROUP_SIZE][item_i % ITEM_GROUP_SIZE] = it_local;
                                
                                // n->FillItemAt(item_i,it_local);
                                // n->items[item_i].comp.data.key = keys[offset];
                                // n->items[item_i].comp.data.value = values[offset];
                            } else {
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                BITMAP_SET(n->child_bitmap, item_i);
                                
                                if(next - offset < Threshold_Array){
                                    n->SetChildAt(item_i,build_tree_nomodel(keys+offset, values+offset, next-offset));
                                    // n->items[item_i].comp.child = build_tree_nomodel(keys+offset, values+offset, next-offset);
                                    // n->items[item_i].comp.child = new subtree(false,true,next-offset,Threshold_Array);
                                }else{
                                    subtree *child_n = new subtree(false,false,next-offset);
                                    n->SetChildAt(item_i,child_n);
                                    // n->items[item_i].comp.child = new subtree(false,false,next-offset);
                                    s.push({begin + offset, begin + next, lvl + 1, child_n});
                                }                                
                            }
                            if (next >= size) {
                                break;
                            } else {
                                item_i = next_i;
                                offset = next;
                            }
                        }
                    }   
                }
                return {ret,max_depth};
            }

            std::pair<subtree*,int> rebuild_tree_FCMD(K *_keys,V * _values,long double slope,long double intercept,int _size){
                //plr means whether to use the model from plr
                //top_slope , top_intercept are the model from the plr
                RT_ASSERT(_size > 1);
                typedef struct {
                        int begin;
                        int end;
                        int lvl; // top lvl = 1
                        subtree* n;
                } Seg;
                std::queue<Seg> s;
                subtree *ret = new subtree(_size == 2,false,_size);
                // subtree* ret = new_subtree(1);
                s.push({0, _size, 1, ret});
                int max_depth = 0;
                while(!s.empty()){
                    const int begin = s.front().begin;
                    const int end = s.front().end;
                    const int lvl = s.front().lvl;
                    max_depth = max(max_depth,lvl);
                    subtree* n = s.front().n;
                    s.pop();
                    #if DEBUG_ASSERT
                    RT_ASSERT(end - begin >= 2);
                    #endif
                    if(end - begin < Threshold_Array  && lvl >1){
                        subtree* _ = build_tree_nomodel(_keys+begin, _values+begin, end-begin);
                        memcpy(n, _, sizeof(subtree));//shalow copy
                        delete _;
                        continue;
                    }
                    if(lvl == 1 && end - begin == 2){
                        subtree* _ = build_tree_two(_keys[begin], _values[begin], _keys[begin+1], _values[begin+1]);
                        memcpy(n,_,sizeof(subtree));
                        delete _;
                        ret = n;
                        continue;
                    }
                    //end - begin > threshold || lvl == 1
                    {
                        RT_ASSERT(n->ordered_array == false);
                        K * keys = _keys + begin;
                        V * values = _values + begin;
                        const int size = end - begin;
                        const int BUILD_GAP_CNT = compute_gap_count(size);
                        n->is_two = 0;
                        n->size.store(size, std::memory_order_release);
                        if(lvl == 1 && slope > 0)
                        {
                            const int L = size * static_cast<int>(BUILD_GAP_CNT);
                            n->slope = slope * (static_cast<long double>(BUILD_GAP_CNT));
                            n->intercept = intercept * (static_cast<long double>(BUILD_GAP_CNT));
                            n->num_items = L;
                        }
                        else
                        {//fmcd
                            const int L = size * static_cast<int>(BUILD_GAP_CNT + 1);
                            int i = 0;
                            int D = 1;
                            RT_ASSERT(D <= size-1-D);
                            double Ut = (static_cast<long double>(keys[size - 1 - D]) - static_cast<long double>(keys[D])) /
                                        (static_cast<double>(L - 2)) + 1e-6;
                            while (i < size - 1 -D){
                                while (i + D < size && keys[i + D] - keys[i] >= Ut) {
                                    i ++;
                                }
                                if(i + D >= size){
                                    break;
                                }
                                D = D + 1;
                                if (D * 3 > size) break;
                                RT_ASSERT(D <= size-1-D);
                                Ut = (static_cast<long double>(keys[size - 1 - D]) - static_cast<long double>(keys[D])) /
                                    (static_cast<double>(L - 2)) + 1e-6;
                            }
                            if (D * 3 <= size) {
                                n->slope = 1.0 / Ut;
                                n->intercept = (L - n->slope * (static_cast<long double>(keys[size - 1 - D]) +
                                                                    static_cast<long double>(keys[D]))) / 2;
                                RT_ASSERT(isfinite(n->slope));
                                RT_ASSERT(isfinite(n->intercept));
                                n->num_items = L;
                            }else{
                                
                                int mid1_pos = (size - 1) / 3;
                                int mid2_pos = (size - 1) * 2 / 3;

                                RT_ASSERT(0 <= mid1_pos);
                                RT_ASSERT(mid1_pos < mid2_pos);
                                RT_ASSERT(mid2_pos < size - 1);

                                const long double mid1_key = (static_cast<long double>(keys[mid1_pos]) +
                                                            static_cast<long double>(keys[mid1_pos + 1])) / 2;
                                const long double mid2_key = (static_cast<long double>(keys[mid2_pos]) +
                                                            static_cast<long double>(keys[mid2_pos + 1])) / 2;

                                n->num_items = size * static_cast<int>(BUILD_GAP_CNT + 1);
                                const double mid1_target = mid1_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;
                                const double mid2_target = mid2_pos * static_cast<int>(BUILD_GAP_CNT + 1) + static_cast<int>(BUILD_GAP_CNT + 1) / 2;

                                n->slope = (mid2_target - mid1_target) / (mid2_key - mid1_key);
                                n->intercept = mid1_target - n->slope * mid1_key;
                                RT_ASSERT(isfinite(n->slope));
                                RT_ASSERT(isfinite(n->intercept));
                            }
                            
                        }        
                        #if DEBUG_ASSERT
                        RT_ASSERT(n->slope >= 0);
                        #endif
                        
                        int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                        if(n->num_items % ((int)ITEM_GROUP_SIZE))
                            row_cnt++;
                        if(row_cnt == 0)
                            row_cnt = 1;
                        n->matrixRow = row_cnt;
                        n->ItemMatrix = new_itemMatrix(row_cnt);
                        
                        int remain_slot = n->num_items;
                        for(int i = 0;i<row_cnt;i++){
                            Item* item_set = nullptr;
                            if(remain_slot >= ITEM_GROUP_SIZE){
                                item_set = new_items_group();
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                                remain_slot -= ITEM_GROUP_SIZE;
                            }else{
                                item_set = new_items(remain_slot);
                                memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                                remain_slot = 0;
                            }
                            n->ItemMatrix[i] = (item_set);
                        }
                        // n->items = new_items(n->num_items);
                        // memset(n->items,0,n->num_items*sizeof(Item));
                        
                        const int bitmap_size = BITMAP_SIZE(n->num_items);
                        n->mlock = new_slock(bitmap_size);
                        for(int i = 0;i<bitmap_size;i++){
                            n->TryLockItem(i*8);
                            n->ReleaseItem(i*8);
                        }
                        n->none_bitmap = new_bitmap(bitmap_size);
                        n->child_bitmap = new_bitmap(bitmap_size);
                        memset(n->none_bitmap, 0xff, sizeof(bitmap_t) * bitmap_size);
                        memset(n->child_bitmap, 0, sizeof(bitmap_t) * bitmap_size);
                        int item_i = n->predict(keys[0]);
                        for (int offset = 0; offset < size; ) {
                            int next = offset + 1, next_i = -1;
                            while (next < size) {  
                                #if DEBUG   
                                if(keys[next] <= keys[next-1]){
                                    cout<<"key unordered"<<endl;
                                }
                                #endif
                                next_i = n->predict( keys[next]);
                                if (next_i == item_i) {
                                    next ++;
                                } else {
                                    break;
                                }
                            }
                            #if DEBUG_ASSERT
                            RT_ASSERT(item_i < n->num_items);
                            #endif
                            if (next == offset + 1) {
                                if(BITMAP_GET(n->none_bitmap,item_i) == 0){
                                    cout<<"bitmap error"<<endl;
                                }
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                Item it_local(keys[offset],values[offset]);
                                n->ItemMatrix[item_i / ITEM_GROUP_SIZE][item_i % ITEM_GROUP_SIZE] = it_local;
                                
                                // n->FillItemAt(item_i,it_local);
                                // n->items[item_i].comp.data.key = keys[offset];
                                // n->items[item_i].comp.data.value = values[offset];
                            } else {
                                #if DEBUG_ASSERT
                                RT_ASSERT(BITMAP_GET(n->none_bitmap,item_i) == 1);
                                RT_ASSERT(BITMAP_GET(n->child_bitmap,item_i) == 0);
                                #endif
                                BITMAP_CLEAR(n->none_bitmap, item_i);
                                BITMAP_SET(n->child_bitmap, item_i);
                                
                                if(next - offset < Threshold_Array){
                                    n->SetChildAt(item_i,build_tree_nomodel(keys+offset, values+offset, next-offset));
                                    // n->items[item_i].comp.child = build_tree_nomodel(keys+offset, values+offset, next-offset);
                                    // n->items[item_i].comp.child = new subtree(false,true,next-offset,Threshold_Array);
                                }else{
                                    subtree *child_n = new subtree(false,false,next-offset);
                                    n->SetChildAt(item_i,child_n);
                                    // n->items[item_i].comp.child = new subtree(false,false,next-offset);
                                    s.push({begin + offset, begin + next, lvl + 1, child_n});
                                }                                
                            }
                            if (next >= size) {
                                break;
                            } else {
                                item_i = next_i;
                                offset = next;
                            }
                        }
                    }   
                }
                return {ret,max_depth};
            }

            //--------------------------Memory pool---------------------------//

            void CreateMemPool(int size_ = 200){
                for(int i = 0 ; i < size_ ; i++){
                    // subtree* n = new_subtree(1);
                    const int slot_item = 8;
                    subtree *n = new subtree(true,false,2,slot_item);
                    int row_cnt = ceil(n->num_items / ITEM_GROUP_SIZE);
                    if(n->num_items % ((int)ITEM_GROUP_SIZE))
                        row_cnt++;
                    if(row_cnt == 0)
                        row_cnt = 1;
                    n->matrixRow = row_cnt;
                    n->ItemMatrix = new_itemMatrix(row_cnt);
                    int remain_slot = n->num_items;
                    for(int i = 0;i<row_cnt;i++){
                        Item* item_set = nullptr;
                        if(remain_slot >= ITEM_GROUP_SIZE){
                            item_set = new_items_group();
                            memset(static_cast<void*>(item_set),0,sizeof(Item)*ITEM_GROUP_SIZE);
                            remain_slot -= ITEM_GROUP_SIZE;
                        }else{
                            item_set = new_items(remain_slot);
                            memset(static_cast<void*>(item_set),0,sizeof(Item)*remain_slot);
                            remain_slot = 0;
                        }
                        n->ItemMatrix[i] = (item_set);
                    }
                    // n->items = new_items(n->num_items);
                    // memset(n->items,0,(n->num_items)*sizeof(Item));
                    n->mlock = new_slock(1);
                    n->TryLockItem(0);
                    n->ReleaseItem(0);
                    n->none_bitmap = new_bitmap(1);
                    n->child_bitmap = new_bitmap(1);
                    n->none_bitmap[0] = 0xff;
                    n->child_bitmap[0] = 0;
                    n->intercept = 0;
                    n->slope = 0;
                    tree_pool.push(n);
                }
            }

            inline bool ReadPool(){
                return lock_pool.load(std::memory_order_acquire);
            }

            inline bool CASPool(bool free = false,bool block=true){
                return lock_pool.compare_exchange_strong(free, block);
            }

            inline void ReleasePool(){
                lock_pool.store(false, std::memory_order_release);
            }
            
            //reset segment max size when build model or split
            // inline void SetSegMax(int slot_,int esize,K key_space){
            //     SegmentMaxSize = min((K)(SEGMENT_MAX_SIZE),key_space);
            //     // SegmentMaxSize = ComputeSegmentMaxSize(slot_,esize,key_space);
            // }

            //--------------------------Space Occupation---------------------------//

            long long SpaceSize(){
                long long space_sum = sizeof(Segment_pt);
                //DataArray
                space_sum += DataArray->SpaceSize();
                //tree_pool
                return space_sum;
            }

            //--------------------------Access on Member Variable ---------------------------//

            //key num
            inline void CreateGroupKeyNumArray(int group_cnt){
                this->group_key_num = new int[group_cnt];
            }

            inline void CreateGroupKeyNumArray(vector<int> group_key){
                this->group_key_num = new int[group_key.size()];
                for(int g = 0;g<group_key.size();g++){
                    this->group_key_num[g] = group_key[g];
                }
            }

            inline void SetGroupKeyNum(int group_i,int k_size){
                __atomic_store_n(&(this->group_key_num[group_i]), k_size, __ATOMIC_SEQ_CST);
            }

            inline void UpdateGroupKeyNum(int group_i){
                int raw = __atomic_load_n(&(this->group_key_num[group_i]),__ATOMIC_ACQUIRE);
                while( !__atomic_compare_exchange_n(&(this->group_key_num[group_i]),&raw,raw+1,true,__ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)){
                    raw = __atomic_load_n(&(this->group_key_num[group_i]),__ATOMIC_ACQUIRE); 
                }
                // printf("%d\n",raw+1);
                // __atomic_fetch_add(&(this->group_key_num[group_i]),1,std::memory_order_relaxed);   
                //(type *ptr, type val, int memorder)
            }
        
            //depth hit cnt
            inline void CreateGroupDepth(int group_cnt){
                this->group_depth = new int[group_cnt];
                memset(this->group_depth,0,sizeof(int)*(group_cnt));
            }

            inline void SetGroupDepth(int group_i){
                // __atomic_store_n(&(this->group_depth[group_i]),MAX_DEPTH,__ATOMIC_SEQ_CST);
                int raw = __atomic_load_n(&(this->group_depth[group_i]),__ATOMIC_ACQUIRE);
                while( !__atomic_compare_exchange_n(&(this->group_depth[group_i]),&raw,raw+1,true,__ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)){
                    raw = __atomic_load_n(&(this->group_depth[group_i]),__ATOMIC_ACQUIRE); 
                }
                // return raw+1;
            }

            inline int GetGroupDepthHitCnt(int group_cnt){
                int sum = 0;
                for(int g = 0;g<group_cnt;g++){
                    sum += __atomic_load_n(&(this->group_depth[g]),__ATOMIC_ACQUIRE);
                }
                return sum;
            }

            //data array
            inline subtree* GetDataArray(){
                return DataArray;
            }

            //SMO atomically set data array
            void SetDataArray(subtree *new_ad){//subtree* old_ad,
                __atomic_store_n(&DataArray, new_ad, __ATOMIC_SEQ_CST);
                for(int _ = 0;_<32;_++){
                    thread_access[_] = 0;
                }
            }
            
            //key num
            //after smo ,update base_key_num
            inline void UpdateBaseKeyNum(int esize){
                base_key_num = esize;
            }

            inline int GetBaseKeyNum(){
                return base_key_num;
            }

            //size bound
            inline void SetSizeBound(){
                this->size_bound = min((int)SEGMENT_MAX_SIZE,this->DataArray->num_items);
                // if(before_smo_blocked <= 5){
                //     this->size_bound = min((int)SEGMENT_MAX_SIZE,max(this->DataArray->num_items,20480));
                // }else{
                //     this->size_bound = min((int)SEGMENT_MAX_SIZE,max(this->DataArray->num_items,10240));
                // }
                // printf("size_bound = %d\n",size_bound);
            }

            inline int GetSizeBound(){
                return this->size_bound;
            }

            //state
            inline bool ReadState(){
                #if STATE_ATOMIC
                return state.load(std::memory_order_acquire);
                #else
                return state;
                #endif
            }

            #if STATE_ATOMIC
            inline bool CASState(bool free = false,bool block=true){
                return state.compare_exchange_strong(free, block);
            }
            #else
            inline bool CASState(){
                /*
                bool __atomic_compare_exchange_n(
                    type *ptr,              // 需要进行比较的ptr
                    type *expected,         // 旧的值，会返回ptr里面的值
                    type desired,           // 想要设置的新的值
                    bool weak,              // 强一致，还是弱一致
                    int success_memorder,   // 成功时的内存序
                    int failure_memorder    // 失败时的内存序
                )
                */
                bool free = false;//,block=true
                return __atomic_compare_exchange_n(&state,&free,true,true,__ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
            }
            #endif

            inline void ResetState(){
                #if STATE_ATOMIC
                state.store(false, std::memory_order_release);
                #else
                __atomic_store_n(&state, false, __ATOMIC_SEQ_CST);
                #endif
                // cout<<this<<" free"<<endl;
            }

            inline void ThreadContentionUpate(const int work_id,int blocked = 1){
                thread_access[work_id]+=blocked;
            }

            /// @brief return the number of thread occured contention 
            /// @return the number of thread occured contention 
            inline int GetThreadContention(){
                int blocked = 0;
                // int res=0;
                for(int _ = 0;_<32;_++){
                    if(thread_access[_])
                        blocked++;
                    // blocked += thread_access[_];
                }
                return min(32,blocked);
            }

            inline int ShowBlocked(){
                int blocked = 0;
                int addictive_key = GetBaseKeyNum();
                int res=0;
                for(int _ = 0;_<32;_++){
                    blocked += thread_access[_];
                }
                printf("blocked:%d\taddictive_key:%d\n",blocked,addictive_key);
            }

            void PrintAllKeys(){
                const int ESIZE = DataArray->size.load();
                K *keys = new K[ESIZE];
                V *values = new V[ESIZE];
                scan_and_destroy_subtree(this->DataArray,keys,values,ESIZE,false);
                for(int i = 0;i<ESIZE;i++){
                    string keys_t = to_string(keys[i])+"\n";
                    write_into_file("./segment_keys.csv",keys_t.c_str());
                }
                delete[] keys;
                delete[] values;
            }

            //--------------------------Member Variable---------------------------//

            K bound;//right guard,the upper bound
            #if STATE_ATOMIC
            std::atomic<bool> state;//indicate whether segment is SMO
            #else
            bool state;
            #endif
            bool last_split;
            int size_bound;
            subtree *DataArray;
            int base_key_num;
            int *group_key_num;
            int *group_depth;
            int thread_access[32];
            std::atomic<bool> lock_pool;
            std::stack<subtree*> tree_pool;
            
            Segment_pt(K base,K bnd,int deta_insert_init = MAX_DEPTH):
                SNode(base,false),bound(bnd),state(false),last_split(false),lock_pool(false){
                for(int _ = 0;_<32;_++){
                    thread_access[_] = 0;
                }
                base_key_num = 0;
                group_depth = nullptr;
                size_bound = 0;
                group_key_num = nullptr;
            }
        };
        struct Index: SNode{
            inline void InitIArray(Index *root,K *keys_array,SNode **values_array,const int n_size,M slope_,M intercept_){
                root->SetDown(values_array[0]);
                
                inodeArray *iarray_ = new inodeArray(n_size,slope_,intercept_);
                inode *ary = iarray_->iArray;
                for(int i = 0;i<n_size;i++){
                    ary[i] = {keys_array[i],values_array[i]};
                }
                root->IArray.store((void*)iarray_,std::memory_order_release);
            }
            
            //get downward_
            SNode* Down() {
                return (downward_.load(std::memory_order_acquire));
                // RT_ASSERT(IArray);
                // return IArray[0].address;
            }

            //set downward_
            void SetDown(SNode* x) {
                downward_.store(x, std::memory_order_release);
            }

            // 这里node 有可能是index，也有可能是segment，统一这样处理了
            // inline void AppendBelow(SNode* below) {
            //     this->SetDown(below);
            // }

            inline bool CASBufferLock(bool free = false,bool block=true){
                return lock_buffer.compare_exchange_strong(free, block);
            }
            
            inline void ReleaseBufferLock(){
                lock_buffer.store(false, std::memory_order_release);
            }

            //-------------reader--------------//
            SNode* FindPrecursor(const uint32_t worker_id, K key){
                inodeArray *array_address  = (inodeArray *)(IArray.load(std::memory_order_acquire));
                inode *ary = array_address->iArray;
                int size = array_address->size;
                // RT_ASSERT(array_address);
                if(!ary)
                    return nullptr;
                PREFETCH(ary[0],0,1);
                int pos = array_address->predict(key);
                if(ary[pos].key == key){
                    return ary[pos].address;
                }
                //buffer中的不去读
                int l = max(0,pos - Gm), r = min(size-1,pos + Gm);
                SNode *res = nullptr;
                while (l <= r){
                    int mid = l + (r-l)/2;
                    K mid_key  = ary[mid].key;
                    if(mid_key == key){
                        return ary[mid].address;
                    }
                    else if(key < mid_key){
                        r = mid-1;
                    }else{
                        res = ary[mid].address;
                        l = mid + 1;
                    }
                }
                return res;
            }

            SNode* FindPrecursor_dif(const uint32_t worker_id, K key){
                inodeArray *array_address  = (inodeArray *)(IArray.load(std::memory_order_acquire));
                inode *ary = array_address->iArray;
                int size = array_address->size;
                // RT_ASSERT(array_address);
                if(!ary)
                    return nullptr;
                PREFETCH(ary[0],0,1);
                int pos = array_address->predict(key - ary[0].key);
                if(ary[pos].key == key){
                    return ary[pos].address;
                }
                //buffer中的不去读

                // Binary
                int l = max(0,pos - Gm), r = min(size-1,pos + Gm);
                SNode *res = nullptr;
                while (l <= r){
                    int mid = l + (r-l)/2;
                    K mid_key  = ary[mid].key;
                    if(mid_key == key){
                        return ary[mid].address;
                    }
                    else if(key < mid_key){
                        r = mid-1;
                    }else{
                        res = ary[mid].address;
                        l = mid + 1;
                    }
                }

                return res;
            }

            SNode* FindPrecursor_dif_debug(const uint32_t worker_id, K key,int &skip){
                inodeArray *array_address  = (inodeArray *)(IArray.load(std::memory_order_acquire));
                inode *ary = array_address->iArray;
                int size = array_address->size;
                // RT_ASSERT(array_address);
                PREFETCH(ary[0],0,1);
                int pos = array_address->predict(key - ary[0].key);
                if(ary[pos].key == key){
                    return ary[pos].address;
                }

                //Binary
                int l = max(0,pos - Gm), r = min(size-1,pos + Gm);
                SNode *res = nullptr;
                while (l <= r){                    
                    int mid = l + (r-l)/2;
                    K mid_key  = ary[mid].key;
                    skip++;
                    if(mid_key == key){
                        return ary[mid].address;
                    }
                    else if(key < mid_key){
                        r = mid-1;
                    }else{
                        res = ary[mid].address;
                        l = mid + 1;
                    }
                    
                }
                return res;
            }

            /// @brief 从pre节点开始找同一层中满足key > node.key的最大的node.key
            /// @param key 
            /// @param pre 
            /// @param level 
            /// @return 
            inline SNode* FindParent(K key,SNode* pre,int level){
                SNode *next_ = pre->Next();
                while(next_ && key >= next_->Key){
                    pre = next_;
                    next_ = pre->Next();
                }
                return pre;
            }

            //----------writer-------------//
            //假定new_index_node 的父节点就是本index node，那么Keys和new_index_node中的第一个元素不需要参与插入
            void Insert(const uint32_t worker_id,std::vector<K> &Keys,std::vector<SNode*> &new_index_node,SNode* preds[],int level,skiplist *list){
                while(1){
                    //check index node to insert,because forward node may split
                    SNode *precur = reinterpret_cast<SNode*>(this);
                    SNode *precur_next = precur->Next();
                    while(precur_next && Keys[0] >= precur_next->Key){
                        precur = precur_next;
                        precur_next = precur->Next();
                    }
                    Index *index_n = reinterpret_cast<Index*>(precur);

                    while(!index_n->CASBufferLock()){;}
                    precur_next = precur->Next();
                    if(precur_next && Keys[0] >= precur_next->Key){
                        index_n->ReleaseBufferLock();
                        continue;
                    }
                    //insert
                    int b_size = index_n->buffer->size(),n_size = new_index_node.size();
                    if(b_size + n_size < MERGE_THRESHOLD){
                        //already got buffer_lock
                        for(int i = 1;i<n_size;i++){
                            index_n->buffer->push_back({Keys[i],new_index_node[i]});
                        }
                        index_n->ReleaseBufferLock();
                        return;
                    }else{
                        inodeArray *array_address  = (inodeArray *)(index_n->IArray.load(std::memory_order_acquire));
                        inode *ary = array_address->iArray;
                        int size = array_address->size;
                        const int new_size = b_size + size + n_size - 1;
                        K *keys_array = new K[new_size];
                        SNode* values_array[new_size];
                        inodeArray *old_array = array_address;
                        // const int old_size = size;

                        index_n->MergeArray(ary,Keys,new_index_node,keys_array,values_array,size,b_size,n_size);
                        //using greedy plr split
                        std::vector<Index*> group;
                        // int split_cnt = index_n->SplitArray(keys_array,values_array,new_size,group);//change IArray,buffer
                        int split_cnt = index_n->SplitArray_spline_preprocess(keys_array,values_array,new_size,group);//change IArray,buffer
                        delete []keys_array;

                        //wait reader thread
                        rcu_barrier(worker_id);
                        // delete old_array;//TODO 暂时不删除

                        //insert into the upper layer index node
                        if(split_cnt > 1 && level < SkiplistMaxLevel){
                            K key_inode = reinterpret_cast<SNode*>(index_n)->Key;
                            // RT_ASSERT(preds[level+1]->Key <= key_inode);//DEBUG
                            Index *pre_inode = reinterpret_cast<Index*>(index_n->FindParent(key_inode,preds[level+1],level));//得到该层的最大前驱(snode.Key<=key_inode)
                            Index *parent_inode = pre_inode;
                            std::vector<K> split_inode_keys;
                            std::vector<SNode*> split_inodes_;
                            for(int i = 0;i<split_cnt;i++){
                                split_inode_keys.push_back(reinterpret_cast<SNode*>(group[i])->Key);
                                split_inodes_.push_back(reinterpret_cast<SNode*>(group[i]));
                            }
                            
                            //实际上只有前驱是head 才需要make parent
                            if(((SNode*)pre_inode)->Key == 0  && list->GetMaxHeight() == level){
                                parent_inode =  new Index(key_inode,index_n);
                                pre_inode->AppendNext(parent_inode,parent_inode);
                                list->UpdateHeight(level+1);
                            }
                            parent_inode->Insert(worker_id,split_inode_keys,split_inodes_,preds,level+1,list);
                        }
                        index_n->ReleaseBufferLock();
                        return;
                    }
                    // ReleaseBufferLock();
                }
            }

            void Merge(inode *ary,int size,std::vector<inode> &middle_array,int b_size){
                int p1 = 0,p2 = 0,p_ = 0;
                while (p1 < size && p2 < b_size){
                    if(ary[p1].key <= buffer->at(p2).key){
                        middle_array[p_] = {ary[p1].key,ary[p1].address};
                        p1++;
                    }else{
                        middle_array[p_] = {buffer->at(p2).key,buffer->at(p2).address};
                        p2++;
                    }
                    p_++;
                }

                while(p1 < size){
                    middle_array[p_] = {ary[p1].key,ary[p1].address};
                    p1++;
                    p_++;
                }

                while(p2 < b_size){
                    middle_array[p_] = {buffer->at(p2).key,buffer->at(p2).address};
                    p2++;
                    p_++;
                }
                return;
            }

            int SplitArray(K *keys_array,SNode **values_array,const int n_size,std::vector<Index*> &group){
                //group:all the index nodes generated from keys_array

                GreedyPLR* plr = new GreedyPLR(Gm);
                vector<Segment*> seg;
                vector<int> segment_stIndex;
                int st = 0,ed = 0;//st marks the begin id of a new segment                

                for (int i = 0; i < n_size; i++) {
                    Segment* seg_res = nullptr;
                    seg_res = plr->Process(static_cast<M>(keys_array[i]), static_cast<M>(i-st));       
                    if(seg_res) {//keys_array[st,i) as a segment
                        segment_stIndex.push_back(st);
                        seg.push_back(seg_res);
                        st = ed = i;
                    }
                    else{
                        ed = i;
                    }
                }
                Segment* seg_res = nullptr;
                seg_res = plr->finish();
                if (seg_res) {
                    segment_stIndex.push_back(st);
                    seg.push_back(seg_res);
                }

                //create new index node
                int new_index_cnt = seg.size();
                // RT_ASSERT(segment_stIndex.size() == new_index_cnt);
                if(new_index_cnt == 1){
                    delete plr;
                    InitIArray(this,keys_array,values_array,n_size,seg[0]->slope,seg[0]->intercept);//atomic change IArray
                    buffer->clear();
                    return 1;
                }
                group.resize(new_index_cnt);
                group[0] = this;
                for(int i = 1;i<new_index_cnt;i++){
                    K *keys_array_ = keys_array + segment_stIndex[i];
                    SNode **values_array_ = values_array + segment_stIndex[i];
                    group[i] = new Index(keys_array_[0]);
                    int i_size;
                    if(i == new_index_cnt -1 ){
                        i_size = n_size - segment_stIndex[i];
                    }else{
                        i_size = segment_stIndex[i+1] - segment_stIndex[i];
                    }
                    InitIArray(group[i],keys_array_,values_array_,i_size,seg[i]->slope,seg[i]->intercept);
                    group[i]->buffer = new std::vector<inode>();
                    //link 1...new_index_cnt-1 at current layer
                    if(i>1)
                        reinterpret_cast<SNode*>(group[i-1])->SetNext(reinterpret_cast<SNode*>(group[i]));
                }
                this->AppendNext(group[1],group[new_index_cnt-1]);
                //atomic change address
                InitIArray(this,keys_array,values_array,segment_stIndex[1],seg[0]->slope,seg[0]->intercept);
                buffer->clear(); 
                delete plr;      
                return new_index_cnt;     
            }

            //using greedy_spline_corridor
            int SplitArray_spline(K *keys_array,SNode **values_array,const int n_size,std::vector<Index*> &group){
                //group:all the index nodes generated from keys_array

                GreedyPLR* plr = new GreedyPLR(Gm);
                vector<std::pair<M,M>> model_groups;
                vector<int> segment_pivot;
                plr->greedy(keys_array,n_size,model_groups,segment_pivot);

                //create new index node
                int new_index_cnt = model_groups.size();
                if(new_index_cnt == 1){
                    delete plr;
                    InitIArray(this,keys_array,values_array,n_size,model_groups[0].first,model_groups[0].second);//atomic change IArray
                    buffer->clear();
                    return 1;
                }
                group.resize(new_index_cnt);
                group[0] = this;
                for(int i = 1;i<new_index_cnt;i++){
                    K *keys_array_ = keys_array + segment_pivot[i];
                    SNode **values_array_ = values_array + segment_pivot[i];
                    group[i] = new Index(keys_array_[0]);
                    int i_size;
                    if(i == new_index_cnt -1 ){
                        i_size = n_size - segment_pivot[i];
                    }else{
                        i_size = segment_pivot[i+1] - segment_pivot[i];
                    }
                    InitIArray(group[i],keys_array_,values_array_,i_size, model_groups[i].first, model_groups[i].second);
                    group[i]->buffer = new std::vector<inode>();
                    //link 1...new_index_cnt-1 at current layer
                    if(i>1)
                        reinterpret_cast<SNode*>(group[i-1])->SetNext(reinterpret_cast<SNode*>(group[i]));
                }
                this->AppendNext(group[1],group[new_index_cnt-1]);
                //atomic change address
                InitIArray(this,keys_array,values_array,segment_pivot[1],model_groups[0].first,model_groups[0].second);
                buffer->clear(); 
                delete plr;      
                return new_index_cnt;     
            }

            //using greedy_spline_corridor with preprocess
            int SplitArray_spline_preprocess(K *keys_array,SNode **values_array,const int n_size,std::vector<Index*> &group){
                //group:all the index nodes generated from keys_array

                GreedyPLR* plr = new GreedyPLR(Gm);
                vector<std::pair<M,M>> model_groups;
                vector<int> segment_pivot;
                plr->greedy_dif(keys_array,n_size,model_groups,segment_pivot);

                //create new index node
                int new_index_cnt = model_groups.size();
                if(new_index_cnt == 1){
                    delete plr;
                    InitIArray(this,keys_array,values_array,n_size,model_groups[0].first,model_groups[0].second);//atomic change IArray
                    buffer->clear();
                    return 1;
                }
                group.resize(new_index_cnt);
                group[0] = this;
                for(int i = 1;i<new_index_cnt;i++){
                    K *keys_array_ = keys_array + segment_pivot[i];
                    SNode **values_array_ = values_array + segment_pivot[i];
                    group[i] = new Index(keys_array_[0]);
                    int i_size;
                    if(i == new_index_cnt -1 ){
                        i_size = n_size - segment_pivot[i];
                    }else{
                        i_size = segment_pivot[i+1] - segment_pivot[i];
                    }
                    InitIArray(group[i],keys_array_,values_array_,i_size, model_groups[i].first, model_groups[i].second);
                    group[i]->buffer = new std::vector<inode>();
                    //link 1...new_index_cnt-1 at current layer
                    if(i>1)
                        reinterpret_cast<SNode*>(group[i-1])->SetNext(reinterpret_cast<SNode*>(group[i]));
                }
                this->AppendNext(group[1],group[new_index_cnt-1]);
                //atomic change address
                InitIArray(this,keys_array,values_array,segment_pivot[1],model_groups[0].first,model_groups[0].second);
                buffer->clear(); 
                delete plr;      
                return new_index_cnt;     
            }

            void MergeArray(inode *ary,std::vector<K> &Keys,std::vector<SNode*> &new_index_node,K *keys_array,SNode **values_array,
                int size,int b_size,int n_size,bool including_first = false){
                sort(buffer->begin(),buffer->end(),cmp);
                std::vector<inode> middle_array(b_size + size);
                Merge(ary,size,middle_array,b_size);
                int p1 = 0,p2 = 0,p_ = 0;
                if(!including_first){
                    p2 = 1;
                }
                int merge_size = b_size + size;
                while (p1 < merge_size && p2 < n_size){
                    if(middle_array[p1].key <= Keys[p2]){
                        keys_array[p_] = middle_array[p1].key;
                        values_array[p_] = middle_array[p1].address;
                        p1++;
                    }else{
                        keys_array[p_] = Keys[p2];
                        values_array[p_] = new_index_node[p2];
                        p2++;
                    }
                    p_++;
                }

                while(p1 < merge_size){
                    keys_array[p_] = middle_array[p1].key;
                    values_array[p_] = middle_array[p1].address;
                    p1++;
                    p_++;
                }

                while(p2 < n_size){
                    keys_array[p_] = Keys[p2];
                    values_array[p_] = new_index_node[p2];
                    p2++;
                    p_++;
                }

            }

            void Show(){
                //start key
                inodeArray *iary = (inodeArray *)(IArray.load(std::memory_order_acquire));
                int size = iary->size;
                inode *ary = iary->iArray;
                cout<<"size:\t"<<size<<std::endl;
                cout<<ary[0].key;
                //键对数量，键对打出来
                for(int i = 1;i<size;i++){
                    cout<<","<<ary[i].key;
                }
                cout<<endl;
            }

            long long SpaceSize(){
                long long space_size = sizeof(Index) - sizeof(lock_buffer);
                //IArray
                void *t = IArray;
                inodeArray *array_s = (inodeArray*)t;
                space_size += array_s->SpaceSize();
                space_size += ((buffer->capacity()) * sizeof(inode));
                return space_size;
            }

            std::atomic<SNode*> downward_; // 下一层SNode,可能是Index, Segment_pt,
            std::atomic<void*> IArray;//inodeArray*,// inode *IArray;//compacted no gap
            std::atomic<bool> lock_buffer;
            std::vector<inode> *buffer;
            Index(K base,SNode *init_add = nullptr):SNode(base,true),downward_(nullptr),IArray(nullptr),
                lock_buffer(false),buffer(nullptr){
                if(init_add){
                    SetDown(init_add);
                    inodeArray *ary = new inodeArray(0,0,base,init_add);
                    IArray.store((void*)ary,std::memory_order_release);
                    buffer = new std::vector<inode>();
                }
            }
        };      
               
        //--------------------------new segment_pt--------------------------//

        SNode* NewSegment_pt(K base,K bound,subtree* n){
            //data array = n,if no data,n = nullptr
            if(!n)
                return NewSegment_pt(base,bound,false);
            SNode *newseg = nullptr;
            // int slots = (n->num_items);
            int ele_size = n->size.load(std::memory_order_acquire);
            if(ele_size < 2){
                newseg = new Segment_pt(base,bound);
            }
            else{
                newseg = new Segment_pt(base,bound,MAX_DEPTH);
            }
            reinterpret_cast<Segment_pt*>(newseg)->DataArray = n;
            reinterpret_cast<Segment_pt*>(newseg)->CreateMemPool();
            reinterpret_cast<Segment_pt*>(newseg)->SetNext(nullptr);
            return newseg;
        }
        
        SNode* NewSegment_pt(K base,K bound,bool ht){
            //ht:is head node or tail node
            SNode *newseg = new Segment_pt(base,bound,MAX_DEPTH);
            reinterpret_cast<Segment_pt*>(newseg)->CreateMemPool();
            //data array = build_tree_none
            if(ht)
                reinterpret_cast<Segment_pt*>(newseg)->DataArray =  reinterpret_cast<Segment_pt*>(newseg)->build_tree_none(base,bound);
            else
                reinterpret_cast<Segment_pt*>(newseg)->DataArray =  reinterpret_cast<Segment_pt*>(newseg)->build_tree_nokey(base,bound);
            reinterpret_cast<Segment_pt*>(newseg)->SetNext(nullptr);
            reinterpret_cast<Segment_pt*>(newseg)->SetSizeBound();
            return newseg;
        }
        

        //--------------------------new index--------------------------//
        //create the multi layer of head/tail 
        SNode* NewIndexBoundArray(int level,K base,K bound,vector<SNode*> &SnodeArray){
            SNode* pr_ = NewSegment_pt(base,bound,true);//bottom segment
            SnodeArray[0] = pr_;
            for(int l = 1;l<=level;l++){
                Index *inode_n = new Index(base,pr_);
                SNode* curr = reinterpret_cast<SNode*>(inode_n);
                curr->SetNext(nullptr);//TODO to delete
                pr_ = curr;
                SnodeArray[l] = curr;
            }
            return pr_;//top index node
        }

        //--------------------------skiplist operation--------------------------//
        
        inline int GetMaxHeight() const {
            return max_height_.load(std::memory_order_acquire);
        }
        
        inline int RandLevel(){
            int lvl = 1;
            default_random_engine e(rd());
            uniform_int_distribution<int>u(1,100);
            for(int i = 0;i<MaxLevel-1;i++){
                if(u(e) > 50){
                    break;
                }
                lvl++;
            }
            return lvl;
        }

        inline void UpdateHeight(int new_height){
            int old_max_height = GetMaxHeight();
            while (new_height > old_max_height) {
                if (max_height_.compare_exchange_weak(old_max_height, new_height)) {
                    // successfully updated it
                    break;
                }
            }
        }

        //for Lookup
        //Scan_debug mark the path and skip in index layer
        SNode* Scan_debug(const uint32_t worker_id,K key,int &path,int &skip,SNode* preds[]){
            SNode* pred = head_;
            SNode* next = nullptr;
            int top_level = GetMaxHeight();
            //down
            pred = head_group[top_level];
            if(top_level){
                pred = pred->Next();
                preds[top_level] = pred;

                #if INDEX_DIF
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif_debug(worker_id,key,skip);
                #else
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                #endif
                top_level--;
                path = 1;
            }
            //get the preds from [top_level,0)
            for(int l = top_level;l>=0;l--){
                //make sure key is geq than pred->Key
                next = pred->Next();
                while(next && key >= next->Key){
                    pred = next;
                    next = next->Next();
                    path++;
                }
                preds[l] = pred;
                //next = nullptr or key <next->Key
                if(l){
                    //TODO DEBUG 数据预处理
                    #if INDEX_DIF
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif_debug(worker_id,key,skip);
                    #else
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                    #endif
                    path++;
                }
            }
            return pred;
        }

        SNode* Scan_debug(const uint32_t worker_id,K key,int &path,int &skip){
            SNode* pred = head_;
            SNode* next = nullptr;
            int top_level = GetMaxHeight();
            //down
            pred = head_group[top_level];
            if(top_level){
                pred = pred->Next();
                #if INDEX_DIF
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif_debug(worker_id,key,skip);
                #else
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                #endif
                top_level--;
                path = 1;
            }
            //get the preds from [top_level,0)
            for(int l = top_level;l>=0;l--){
                //make sure key is geq than pred->Key
                next = pred->Next();
                while(next && key >= next->Key){
                    pred = next;
                    next = next->Next();
                    path++;
                }
                //next = nullptr or key <next->Key
                if(l){
                    #if INDEX_DIF
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif_debug(worker_id,key,skip);
                    #else
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                    #endif
                    path++;
                }
            }
            return pred;
        }

        SNode* Scan(const uint32_t worker_id,K key,SNode* preds[]){
            SNode* pred = head_;
            SNode* next = nullptr;
            int top_level = GetMaxHeight();
            //down
            pred = head_group[top_level];
            if(top_level){
                pred = pred->Next();
                preds[top_level] = pred;

                #if INDEX_DIF
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif(worker_id,key);
                #else
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                #endif
                top_level--;
            }
            //get the preds from [top_level,0)
            for(int l = top_level;l>=0;l--){
                //make sure key is geq than pred->Key
                next = pred->Next();
                while(next && key >= next->Key){
                    pred = next;
                    next = next->Next();
                }
                preds[l] = pred;
                //next = nullptr or key <next->Key
                if(l){
                    //TODO DEBUG 数据预处理
                    #if INDEX_DIF
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif(worker_id,key);
                    #else
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                    #endif
                }
            }
            return pred;
        }

        SNode* Scan(const uint32_t worker_id,K key){
            SNode* pred = head_;
            SNode* next = nullptr;
            int top_level = GetMaxHeight();
            //down
            pred = head_group[top_level];
            if(top_level){
                pred = pred->Next();
                #if INDEX_DIF
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif(worker_id,key);
                #else
                pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                #endif
                top_level--;
            }
            //get the preds from [top_level,0)
            for(int l = top_level;l>=0;l--){
                //make sure key is geq than pred->Key
                next = pred->Next();
                while(next && key >= next->Key){
                    pred = next;
                    next = next->Next();
                }
                //next = nullptr or key <next->Key
                if(l){
                    #if INDEX_DIF
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor_dif(worker_id,key);
                    #else
                    pred = reinterpret_cast<Index*>(pred)->FindPrecursor(worker_id,key);
                    #endif
                }
            }
            return pred;
        }

        //TODO reclamation
        //skiplist lookup a key
        std::pair<bool,V> Lookup_pessimistic(const uint32_t worker_id,K key){
            rcu_progress(worker_id);
            // SNode* preds[MaxLevel+1];
            // for(int i =0;i<=MaxLevel;i++){
            //     preds[i] = head_group[i];
            // }
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan(worker_id,key));
            while(true){
                if(locate->bound > key){
                    return locate->DataArray->find_key_in_subtree_pessimistic(key);
                }
                locate = reinterpret_cast<Segment_pt*>(locate->Next());
            }
            return {false,0};
        }

        std::pair<bool,V> Lookup_optimistic(const uint32_t worker_id,K key){
            rcu_progress(worker_id);
            // SNode* preds[MaxLevel+1];
            // for(int i =0;i<=MaxLevel;i++){
            //     preds[i] = head_group[i];
            // }
            // Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan(worker_id,key));
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan(worker_id,key));
            while(true){
                if(locate->bound > key){
                    return locate->DataArray->find_key_in_subtree_optimistic(key);
                }
                locate = reinterpret_cast<Segment_pt*>(locate->Next());
            }
            return {false,0};
        }

        std::pair<bool,V> Lookup_optimistic_debug(const uint32_t worker_id,K key,int &path,int &skip,int &depth,int &binary_skip){
            path = skip = depth =binary_skip = 0;
            rcu_progress(worker_id);
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan_debug(worker_id,key,path,skip));
            while(true){
                if(locate->bound > key){
                    return locate->DataArray->find_key_in_subtree_optimistic_debug(key,depth,binary_skip);
                }
                locate = reinterpret_cast<Segment_pt*>(locate->Next());
            }
            return {false,0};
        }
       
        void Lookup(const uint32_t worker_id,K low_bound,int key_num,std::vector<std::pair<K,V>> &result){
            rcu_progress(worker_id);
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan(worker_id,low_bound));
            int remain_cnt = key_num;
            while(true){
                if(locate->bound > low_bound){
                    int size_scan_res =  locate->DataArray->ScanKeys(low_bound,remain_cnt,result);
                    remain_cnt -= size_scan_res;
                    if(remain_cnt <= 0){
                        return;
                    }
                }
                locate = reinterpret_cast<Segment_pt*>(locate->Next());
            }
            return ;
        }        

        bool Add(const uint32_t worker_id,K key,V value){
            //step1 find segment
            rcu_progress(worker_id);
            SNode* preds[MaxLevel+1];
            for(int i =0;i<=MaxLevel;i++){
                preds[i] = head_group[i];
            }
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan(worker_id,key,preds));
            bool worker_blocked = false;
            while(true){    
                if(key < locate->bound){//skip when the bound of locate segment is smaller than key because of splitting
                    //step2 check state
                    
                    #if CONFLICT_YIELD
                    // CheckStateYield(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    long loop_cnt = 0;
                    int mod_cnt = 50;
                    while(1){
                        while(node_busy){
                            if(loop_cnt%mod_cnt == 0){
                                loop_cnt = 0;
                                mod_cnt = max(20,mod_cnt/2);
                                #if UTILITY_SMO
                                locate->ThreadContentionUpate(mod_cnt);
                                #endif
                                std::this_thread::yield();
                            }
                            loop_cnt++;
                            //wait a second
                            node_busy = locate->ReadState();
                        }
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    if(loop_cnt)
                        worker_blocked = true;
                    #else
                    // CheckState(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    uint64_t address_ = (uint64_t)((void*)(locate));
                    long loop_cnt = 0;
                    while(1){
                        while(node_busy){
                            if(!loop_cnt)
                                rcu_status[worker_id].waiting_node = address_;
                            //wait a second
                            node_busy = locate->ReadState();
                            loop_cnt++;
                        }
                        #if UTILITY_SMO
                        if(loop_cnt)
                            locate->ThreadContentionUpate(worker_id,loop_cnt);
                        #endif
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    rcu_status[worker_id].waiting_node = 0;
                    if(loop_cnt)
                        worker_blocked = true;
                    #endif
                    
                    if(key < locate->bound){
                        //step3 do insert
                        int depth = 0;
                        #if UTILITY_SMO
                        locate->ThreadContentionUpate(worker_id);
                        #endif
                        int group_id = -1;
                        locate->insert_subtree_optimistic(key,value,route[worker_id],depth,worker_blocked,group_id);
                        if(group_id >= 0){
                            if(depth >= MAX_DEPTH){
                                locate->SetGroupDepth(group_id);
                            }
                            locate->UpdateGroupKeyNum(group_id);
                        }
                        //TODO DEBUG
                        if(worker_blocked)
                            locate->ThreadContentionUpate(worker_id);

                        bool smo = false;
                        if(depth >= MAX_DEPTH){
                            int after_insert_size = locate->DataArray->size;
                            int increased = after_insert_size - locate->GetBaseKeyNum();
                            int capacity = locate->GetSizeBound();
                            int hit_cnt = locate->GetGroupDepthHitCnt(locate->DataArray->matrixRow);
                            smo = ((after_insert_size*2 >= capacity && hit_cnt*100 >= (increased) )
                                    || after_insert_size >= capacity
                                );
                            if(smo){
                                //if detect segment is not doing SMO,try to change state
                                int try_cnt = 0;
                                while(locate->last_split || !locate->CASState()){
                                    for(int loop_ = 0;loop_<1000;loop_++){;}
                                    try_cnt++;
                                    if(locate->ReadState() || try_cnt > 100){
                                        smo = false;
                                        break;
                                    }
                                }
                            }
                        }

                        //step5 switch rcu status
                        rcu_write_free(worker_id);//->waiting
                        if(!smo)
                            return true;
                        //step6 wait other writers in this segment before state change 
                        rcu_writer_barrier(worker_id);
                        //step7 do rebuild
                        int before_smo_blocked= 0,split_cnt = 0;
                        #if CLOCK_MARK
                        const auto start_time = std::chrono::steady_clock::now();
                        #endif
                        RebuildSegmentFast(worker_id,preds,locate,before_smo_blocked,split_cnt);
                        //step8 reset state
                        locate->ResetState();
                        #if CLOCK_MARK
                        const auto end_time = std::chrono::steady_clock::now();
                        const auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time);
                        rebuild_time[worker_id] += duration.count();
                        #endif
                        return true;
                    }else{//skip
                        rcu_write_free(worker_id);
                    }
                }
                //skip 
                SNode* next = locate->Next();
                locate = reinterpret_cast<Segment_pt*>(next);
            }
            
            return false;
        }

        bool Add_debug(const uint32_t worker_id,K key,V value,int &path,int &skip,int &depth,long long &loop_cnt,int &rebuild_cnt){
            path = 0,skip = 0,depth = 0,loop_cnt = 0,rebuild_cnt=0;
            //step1 find segment
            rcu_progress(worker_id);
            SNode* preds[MaxLevel+1];
            for(int i =0;i<=MaxLevel;i++){
                preds[i] = head_group[i];
            }
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan_debug(worker_id,key,path,skip,preds));
            bool worker_blocked = false;
            while(true){    
                if(key < locate->bound){//skip when the bound of locate segment is smaller than key because of splitting
                    //step2 check state
                    
                    #if CONFLICT_YIELD
                    // CheckStateYield(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    long loop_cnt = 0;
                    int mod_cnt = 50;
                    while(1){
                        while(node_busy){
                            if(loop_cnt%mod_cnt == 0){
                                loop_cnt = 0;
                                mod_cnt = max(20,mod_cnt/2);
                                #if UTILITY_SMO
                                locate->ThreadContentionUpate(mod_cnt);
                                #endif
                                std::this_thread::yield();
                            }
                            loop_cnt++;
                            //wait a second
                            node_busy = locate->ReadState();
                        }
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    if(loop_cnt)
                        worker_blocked = true;
                    #else
                    // CheckState(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    uint64_t address_ = (uint64_t)((void*)(locate));
                    // long loop_cnt = 0;
                    while(1){
                        while(node_busy){
                            if(!loop_cnt)
                                rcu_status[worker_id].waiting_node = address_;
                            //wait a second
                            node_busy = locate->ReadState();
                            loop_cnt++;
                        }
                        #if UTILITY_SMO
                        if(loop_cnt)
                            locate->ThreadContentionUpate(worker_id,loop_cnt);
                        #endif
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    rcu_status[worker_id].waiting_node = 0;
                    if(loop_cnt)
                        worker_blocked = true;
                    #endif
                    
                    if(key < locate->bound){
                        //step3 do insert
                        // int depth = 0;
                        #if UTILITY_SMO
                        locate->ThreadContentionUpate(worker_id);
                        #endif
                        int group_id = -1;
                        locate->insert_subtree_optimistic(key,value,route[worker_id],depth,worker_blocked,group_id);
                        if(group_id >= 0){
                            if(depth >= MAX_DEPTH){
                                locate->SetGroupDepth(group_id);
                            }
                            locate->UpdateGroupKeyNum(group_id);
                        }
                        // locate->insert_subtree(key,value,route[worker_id],depth);
                        //TODO DEBUG
                        if(worker_blocked)
                            locate->ThreadContentionUpate(worker_id);

                        bool smo = false;
                        if(depth >= MAX_DEPTH){
                            int after_insert_size = locate->DataArray->size;
                            int increased = after_insert_size - locate->GetBaseKeyNum();
                            int capacity = locate->GetSizeBound();
                            int hit_cnt = locate->GetGroupDepthHitCnt(locate->DataArray->matrixRow);
                            smo = ((after_insert_size*2 >= capacity && hit_cnt*100 >= (increased) )
                                    ||
                                after_insert_size >= capacity
                                );
                            if(smo){
                                //if detect segment is not doing SMO,try to change state
                                int try_cnt = 0;
                                while(locate->last_split || !locate->CASState()){
                                    for(int loop_ = 0;loop_<1000;loop_++){;}
                                    try_cnt++;
                                    if(locate->ReadState() || try_cnt > 100){
                                        smo = false;
                                        break;
                                    }
                                }
                            }
                        }

                        //step5 switch rcu status
                        rcu_write_free(worker_id);//->waiting
                        if(!smo)
                            return true;
                        //step6 wait other writers who got into segment before state change 
                        rcu_writer_barrier(worker_id);
                        //step7 do rebuild
                        // RebuildSegment(worker_id,preds,locate);
                        // int rebuild_part = locate->DataArray->predict(key);
                        int before_smo_blocked= 0;
                        // after_insert_size = locate->DataArray->size;
                        #if CLOCK_MARK
                        const auto start_time = std::chrono::steady_clock::now();
                        #endif
                        // SMOSelect(worker_id,preds,locate,smo);
                        int split_cnt = 0;
                        bool do_split = RebuildSegmentFast(worker_id,preds,locate,before_smo_blocked,split_cnt);
                        rebuild_cnt++;
                        //TODO DEBUG check blocked thread
                        // int sum_blocked_thread = 0;
                        // for(int tid = 0;tid<32;tid++){
                        //     if(rcu_status[tid].waiting_node == address_){
                        //         sum_blocked_thread++;
                        //     }
                        // }
                        // printf("%"PRIu64" with key num=%d after smo sum_blocked_thread = %d increased with %d\n",
                        //     address_,after_insert_size,
                        //     sum_blocked_thread,sum_blocked_thread-before_smo_blocked);
                        //step8 reset state
                        locate->ResetState();
                        #if CLOCK_MARK
                        if(do_split){
                            const auto end_time = std::chrono::steady_clock::now();
                            const auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(end_time - start_time);
                            printf("%d\t%d\t%d\n",after_insert_size,split_cnt,duration.count());
                            rebuild_time[worker_id] += duration.count();
                        }
                        #endif
                        return true;
                    }else{//skip
                        rcu_write_free(worker_id);
                    }
                }
                //skip 
                SNode* next = locate->Next();
                locate = reinterpret_cast<Segment_pt*>(next);
            }
            
            return false;	
        }

        bool Update(const uint32_t worker_id,K key,V value){
            //step1 find segment
            rcu_progress(worker_id);
            SNode* preds[MaxLevel+1];
            for(int i =0;i<=MaxLevel;i++){
                preds[i] = head_group[i];
            }
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan(worker_id,key,preds));
            while(true){    
                if(key < locate->bound){//skip when the bound of locate segment is smaller than key because of splitting
                    //step2 check state 
                    #if CONFLICT_YIELD
                    // CheckStateYield(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    int spin_cnt = 1;
                    int mod_cnt = 50;
                    while(1){
                        while(node_busy){
                            if(spin_cnt%mod_cnt == 0){
                                spin_cnt = 0;
                                mod_cnt = max(20,mod_cnt/2);
                                #if UTILITY_SMO
                                locate->ThreadContentionUpate(mod_cnt);
                                #endif
                                std::this_thread::yield();
                            }
                            spin_cnt++;
                            //wait a second
                            node_busy = locate->ReadState();
                        }
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    #else
                    // CheckState(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    long loop_cnt = 0;
                    while(1){
                        while(node_busy){
                            //wait a second
                            node_busy = locate->ReadState();
                            loop_cnt++;
                        }
                        #if UTILITY_SMO
                        if(loop_cnt)
                            locate->ThreadContentionUpate(worker_id,loop_cnt);
                        #endif
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    #endif
                    
                    if(key < locate->bound){
                        //step3 do insert
                        int depth = 0;
                        #if UTILITY_SMO
                        locate->ThreadContentionUpate(worker_id);
                        #endif
                        bool res = locate->Update(key,value);
                        rcu_write_free(worker_id);//->waiting
                        return res;
                    }else{//skip
                        rcu_write_free(worker_id);
                    }
                }
                //skip 
                SNode* next = locate->Next();
                locate = reinterpret_cast<Segment_pt*>(next);
            }
            return false;	
        }

        bool Delete(const uint32_t worker_id,K key,V value){
            //step1 find segment
            rcu_progress(worker_id);
            SNode* preds[MaxLevel+1];
            for(int i =0;i<=MaxLevel;i++){
                preds[i] = head_group[i];
            }
            Segment_pt* locate = reinterpret_cast<Segment_pt*>(Scan(worker_id,key,preds));
            while(true){    
                if(key < locate->bound){//skip when the bound of locate segment is smaller than key because of splitting
                    //step2 check state 
                    #if CONFLICT_YIELD
                    // CheckStateYield(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    int spin_cnt = 1;
                    int mod_cnt = 50;
                    while(1){
                        while(node_busy){
                            if(spin_cnt%mod_cnt == 0){
                                spin_cnt = 0;
                                mod_cnt = max(20,mod_cnt/2);
                                #if UTILITY_SMO
                                locate->ThreadContentionUpate(mod_cnt);
                                #endif
                                std::this_thread::yield();
                            }
                            spin_cnt++;
                            //wait a second
                            node_busy = locate->ReadState();
                        }
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    #else
                    // CheckState(worker_id,locate);
                    bool node_busy = locate->ReadState();
                    long loop_cnt = 0;
                    while(1){
                        while(node_busy){
                            //wait a second
                            node_busy = locate->ReadState();
                            loop_cnt++;
                        }
                        #if UTILITY_SMO
                        if(loop_cnt)
                            locate->ThreadContentionUpate(worker_id,loop_cnt);
                        #endif
                        rcu_write_busy(worker_id);//->active
                        node_busy = locate->ReadState();
                        if(!node_busy){
                            break;
                        }
                        rcu_write_free(worker_id);//->blocked
                    }
                    #endif
                    
                    if(key < locate->bound){
                        //step3 do insert
                        int depth = 0;
                        #if UTILITY_SMO
                        locate->ThreadContentionUpate(worker_id);
                        #endif
                        bool res = locate->Delete(key,value,route[worker_id]);
                        rcu_write_free(worker_id);//->waiting
                        return res;
                    }else{//skip
                        rcu_write_free(worker_id);
                    }
                }
                //skip 
                SNode* next = locate->Next();
                locate = reinterpret_cast<Segment_pt*>(next);
            }
            return false;
        }

        bool RebuildSegmentFast(const uint32_t worker_id,SNode** preds,Segment_pt* locate,int &before_smo_blocked,int &split_cnt){
            subtree *n = locate->DataArray;
            const int ESIZE = n->size.load(std::memory_order_acquire);
            K n_start = reinterpret_cast<SNode*>(locate)->Key;
            K n_stop = locate->bound;
            uint64_t address_ = (uint64_t)((void*)(locate));
            for(int tid = 0;tid<32;tid++){
                if(rcu_status[tid].waiting_node == address_){
                    before_smo_blocked++;
                }
            }
            // printf("%"PRIu64" before smo before_smo_blocked = %d\n",address_,before_smo_blocked);
            //TODO split static
            //utility
            // int contention_thread = locate->GetThreadContention();
            // int split_num = getSplitK(before_smo_blocked,MAX_DEPTH) ;
            int split_num = max(int(SPLIT_STATIC),(int)(ESIZE/SEGMENT_MAX_SIZE));
            int capacity = locate->GetSizeBound();
            bool WhetherSplit= ( (ESIZE*2 >= capacity && before_smo_blocked >=15 ) 
                        || ((ESIZE ) >= capacity) );
            // int hit_cnt = locate->GetGroupDepthHitCnt(locate->DataArray->matrixRow);
            // int size_bound = locate->GetSizeBound();
            // printf("[%u-%u] do smo op:%d\t increase key num = %u\thit cnt = %d\tsize bound=%d\tsplit num=%d\tbefore_smo_blocked = %d\n",
            //     n_start,n_stop,
            //     WhetherSplit,
            //     ESIZE-locate->GetBaseKeyNum(),hit_cnt,size_bound,split_num,before_smo_blocked);
            // bool WhetherSplit= (!(locate->next_rebuild) && (ESIZE >= SEGMENT_MAX_SIZE || (ESIZE>1000 && split_num > 1)) ) ;
            // (split_num > 1 );
            //| ESIZE >= SEGMENT_MAX_SIZE);
            // && !(locate->next_rebuild));
            // printf("key num %d\tWhetherSplit:%d\n",ESIZE,WhetherSplit);
            //     (ESIZE >= SEGMENT_MAX_SIZE || 
            //     split_num > 1);
            if(WhetherSplit && n->matrixRow > 1){
                std::vector<SNode*> split_nodes;
                std::vector<K> inode_keys;
                WhetherSplit = SplitFast(locate,n_start,n_stop,split_nodes,inode_keys,split_num,before_smo_blocked);
                if(WhetherSplit){
                    split_cnt = split_num;
                    SNode *pre_inode = reinterpret_cast<Index*>(preds[1])->FindParent(n_start,preds[1],1);
                    Index *parent_inode = reinterpret_cast<Index*>(pre_inode);
                    if(pre_inode->Key == 0 && pre_inode->Next()->Key == KeyMax ){
                        SNode *pre_inode_next = (pre_inode)->Next();
                        RT_ASSERT(pre_inode_next == nullptr || (inode_keys.back() < pre_inode_next->Key));
                        //create a new index
                        parent_inode =  new Index(n_start,split_nodes[0]);
                        pre_inode->AppendNext(parent_inode,parent_inode);
                        UpdateHeight(1);
                    }
                    //TODO sample index
                    #if INDEX_SAMPLE
                    std::vector<SNode*> split_nodes_samples;
                    std::vector<K> inode_keys_samples;
                    for(int i = 0;i<split_num;i++){
                        if(i%2 == 0){
                            split_nodes_samples.push_back(split_nodes[i]);
                            inode_keys_samples.push_back(inode_keys[i]);
                        }else{
                            ((Segment_pt*)split_nodes[i])->last_split = false;
                        }
                    }
                    parent_inode->Insert(worker_id,inode_keys_samples,split_nodes_samples,preds,1,this);
                    for(int sg_id = 1;sg_id<split_nodes_samples.size();sg_id++){
                        ((Segment_pt*)split_nodes_samples[sg_id])->last_split = false;
                    }
                    #else
                    parent_inode->Insert(worker_id,inode_keys,split_nodes,preds,1,this);
                    for(int sg_id = 1;sg_id<split_nodes.size();sg_id++){
                        ((Segment_pt*)split_nodes[sg_id])->last_split = false;
                    }
                    #endif
                    return true;
                }
            }
            K *keys = new K[ESIZE];
            V *values = new V[ESIZE];
            locate->scan_and_destroy_subtree(n,keys,values,ESIZE,false);
            vector<int> after_smo_group_key;
            // std::pair<subtree*,int> res_ = locate->rebuild_tree(keys,values,ESIZE);
            std::pair<subtree*,int> res_ = locate->rebuild_tree_FCMD(keys,values,ESIZE,after_smo_group_key);
            if(locate->group_key_num){
                delete[] locate->group_key_num;
            }
            locate->CreateGroupKeyNumArray(after_smo_group_key);
            delete[] locate->group_depth;
            locate->CreateGroupDepth(after_smo_group_key.size());
            locate->SetDataArray(res_.first);
            locate->SetSizeBound();
            locate->UpdateBaseKeyNum(ESIZE);
            delete[] keys;
            delete[] values;
            return false;
        }

        //fast split ,keep origin model & subtree but insert new node into index layer
        bool SplitFast(Segment_pt *root,K _start,K _stop,
                std::vector<SNode*> &split_nodes,std::vector<K> &inode_keys,int &split_num,int before_smo_blocked){
            //TODO 因为model failure 会导致当我们想要将Items划分成s个部分时，
            //出现前k个部分不仅根本没有key，而且使用model得到这些部分的bound后，bound超出了start的边界 
            
            subtree *root_da = root->GetDataArray();
            int slot_all = root_da->num_items;
            int slot_partition = ITEM_GROUP_SIZE;
            if(split_num <= 1){
                split_num = min(root_da->matrixRow,SPLIT_STATIC);
                slot_partition = (int(root_da->matrixRow * 1.0 / split_num)) * ITEM_GROUP_SIZE;
            }else{
                if(split_num < root_da->matrixRow){
                    slot_partition = (int(root_da->matrixRow * 1.0 / split_num)) * ITEM_GROUP_SIZE;
                }else{
                    split_num = root_da->matrixRow;
                }
            }
            
            // split_num = root_da->matrixRow;
            // if(split_num >= 10){
            //     slot_partition = (root_da->matrixRow / 10) * ITEM_GROUP_SIZE;
            //     split_num = 10;
            // }
            
            //TODO PRINT
            // printf("%d\n",split_num);
            // cout<<"split_num = matrixRow: "<<split_num<<endl;
            
            int offset = 0;//make sure offset|8
            K segment_head_bound = _stop;     

            // skip part whose region out of bound
            int real_start = -1;
            for(int i = 0;i<split_num;i++){
                int slot_part = slot_partition;
                if(i < split_num-1){
                    offset += slot_part;
                    K tmp = root_da->GetRangeBound(offset);
                    if( tmp > _start && tmp <= _stop){
                        segment_head_bound = tmp;
                        real_start = i;
                        offset -= slot_part;
                        break;
                    }
                }else{
                    real_start = i;
                    return false;
                }
            }
            split_num-=real_start;
            // printf("%d\n",split_num);
            split_nodes.resize(split_num);//segment group
            inode_keys.resize(split_num);//index node group
            split_nodes[0] = root;

            int remain_slot = slot_all - offset;
            RT_ASSERT(offset % 8 == 0);
            RT_ASSERT((BITMAP_SIZE(slot_all) - BITMAP_SIZE(offset)) == BITMAP_SIZE(remain_slot));
            int bitmap_cnt_remain = BITMAP_SIZE(slot_all) - BITMAP_SIZE(offset);

            int size_all = root_da->size.load();
            // Item *items_raw = root_da->items;
            Item **itemMatrix_raw = root_da->ItemMatrix;
            int *group_key_num_raw = root->group_key_num;
            int *group_depth_raw = root->group_depth;
            bitmap_t *none_bitmap_raw = root_da->none_bitmap;
            bitmap_t *child_bitmap_raw = root_da->child_bitmap;
            slock *lock_raw = root_da->mlock;
            K last_partition_bound = segment_head_bound;
            int remain_size = size_all;
            int root_node_esize = 0;
            bool root_next_rebuild = false;
            subtree *root_dataarray=nullptr;
            for(int i =0;i<split_num;i++){//start from offset
                //region is corrosponding to items_raw[offset,offset+slot_part)
                int slot_part = slot_partition;
                RT_ASSERT(slot_part % 8 == 0);
                RT_ASSERT(offset %8 == 0);
                RT_ASSERT(BITMAP_SIZE(slot_part) ==  slot_part/8);
                if(i == split_num-1)
                    slot_part = slot_all - offset;            
                remain_slot-=slot_part;
                
                K base_n,bound_n;
                if(i){
                    base_n = last_partition_bound;
                    RT_ASSERT(base_n > _start);
                    if(i<split_num-1){
                        bound_n = root_da->GetRangeBound(offset+slot_part);
                        bound_n = min(bound_n,_stop);
                    }else{
                        bound_n = _stop;
                    }
                }else{
                    base_n = _start;
                    bound_n = segment_head_bound;
                    RT_ASSERT(last_partition_bound > _start && last_partition_bound < _stop);
                }
                
                if(bound_n == _stop && i < split_num-1 && bound_n > base_n){
                    split_num = i+1;
                    split_nodes.resize(split_num);//segment group
                    inode_keys.resize(split_num);//index node group
                }
                
                RT_ASSERT(bound_n > base_n && bound_n <= _stop);
                last_partition_bound = bound_n;


                //items
                int row_cnt = ceil(slot_part / ITEM_GROUP_SIZE);
                if(slot_part % (int(ITEM_GROUP_SIZE)))
                    row_cnt++;
                //size 
                int key_num_partition = 0;
                Item **itemMatrix_n = root->new_itemMatrix(row_cnt);
                vector<int> group_key_num_n(row_cnt);
                for(int j = 0,base_matrix = offset/ITEM_GROUP_SIZE;j<row_cnt;j++){
                    itemMatrix_n[j] = itemMatrix_raw[base_matrix+j];
                    group_key_num_n[j] = group_key_num_raw[base_matrix+j];
                    key_num_partition += group_key_num_n[j];
                }
                // Item *item_n = root->new_items(slot_part);
                // memcpy(item_n,items_raw + offset,sizeof(Item)*(slot_part));
                // memset(item_n,0,(slot_part)*sizeof(Item));

                // bitmap
                const int bitmap_size_n = (BITMAP_SIZE(slot_part));
                bitmap_cnt_remain-=(bitmap_size_n);
                bitmap_t *none_bitmap_n = root->new_bitmap(bitmap_size_n);
                bitmap_t *child_bitmap_n = root->new_bitmap(bitmap_size_n);
                // memset(none_bitmap_n, 0xff, sizeof(bitmap_t) * bitmap_size_n);
                // memset(child_bitmap_n, 0, sizeof(bitmap_t) * bitmap_size_n);
                memcpy(none_bitmap_n,none_bitmap_raw + (BITMAP_SIZE(offset)), sizeof(bitmap_t)*(bitmap_size_n)  );
                memcpy(child_bitmap_n,child_bitmap_raw + (BITMAP_SIZE(offset)), sizeof(bitmap_t)*(bitmap_size_n)  );

                // locks
                slock *mlock_n = root->new_slock(bitmap_size_n);
                for(int j = 0;j<bitmap_size_n;j++){
                    mlock_n[j].try_lock();
                    mlock_n[j].unlock(); 
                }

                //size 
                // int key_num_partition_check = 0;
                // if(i == split_num-1){
                //     key_num_partition_check = remain_size;
                // }else{
                //     for(int j = 0;j<slot_part;j++){
                //         if(BITMAP_GET(none_bitmap_raw,offset+j) == 0){
                //             if(BITMAP_GET(child_bitmap_raw,offset+j) == 0){
                //                 key_num_partition_check++;
                //             }else{
                //                 key_num_partition_check += (root_da->GetItemAt(offset+j).comp.child->size.load(std::memory_order_acquire));
                //             }
                //         }
                //     }
                // }
                // RT_ASSERT(key_num_partition_check == key_num_partition);
                remain_size-=key_num_partition;

                subtree *new_subtree = new subtree(false,false,key_num_partition,slot_part);
                new_subtree->ordered_array = false;
                new_subtree->matrixRow = row_cnt;
                new_subtree->ItemMatrix = itemMatrix_n;
                // new_subtree->items = item_n;
                new_subtree->none_bitmap = none_bitmap_n;
                new_subtree->child_bitmap = child_bitmap_n;
                new_subtree->mlock = mlock_n;
                new_subtree->slope = root_da->slope;
                new_subtree->intercept = root_da->intercept - static_cast<long double>(offset);
                offset += slot_part;
                if(i){
                    //base bound
                    // K base_n = last_partition_bound;
                    // K bound_n;
                    inode_keys[i] = base_n;
                    // if(i < split_num-1){
                    //     bound_n = root_da->GetRangeBound(offset);
                    //     bound_n = min(bound_n,_stop);
                    // }
                    // else{
                    //     bound_n = _stop;
                    // }
                    // RT_ASSERT(base_n > _start);
                    // if(bound_n <= base_n || bound_n > _stop){
                    //     cout<<"debug"<<endl;
                    // }
                    // RT_ASSERT(bound_n > base_n && bound_n <= _stop);
                    // last_partition_bound = bound_n;
                    
                    //new segment
                    SNode* next_seg = NewSegment_pt(base_n,bound_n,new_subtree);
                    split_nodes[i] = next_seg;
                    if(i>1){
                        split_nodes[i-1]->SetNext(next_seg);
                    }
                    ((Segment_pt*)(next_seg))->last_split = true;
                    ((Segment_pt*)(next_seg))->CreateGroupKeyNumArray(group_key_num_n);
                    ((Segment_pt*)(next_seg))->CreateGroupDepth(row_cnt);
                    ((Segment_pt*)(next_seg))->UpdateBaseKeyNum(key_num_partition);
                    ((Segment_pt*)(next_seg))->SetSizeBound();
                }else{
                    inode_keys[i] = _start;
                    // RT_ASSERT(last_partition_bound > _start && last_partition_bound < _stop);
                    root_dataarray = new_subtree;
                    root_node_esize = key_num_partition;
                    root->CreateGroupKeyNumArray(group_key_num_n);
                    root->CreateGroupDepth(row_cnt);
                }
            }
            RT_ASSERT(remain_size == 0);
            if(split_num > 1){
                //link the bottom(segment_pt)
                split_nodes[split_num-1]->SetNext(root->Next());
                root->SetNext(split_nodes[1]);
                //2.7 update root(segment_pt)
                root->bound = segment_head_bound;
                root->SetDataArray(root_dataarray);
            }else{
                root->SetDataArray(root_dataarray);
            }
            root->SetSizeBound();
            root->UpdateBaseKeyNum(root_node_esize);
            delete[] group_key_num_raw;
            delete[] group_depth_raw;
            root->delete_bitmap(none_bitmap_raw,BITMAP_SIZE(slot_all));
            root->delete_bitmap(child_bitmap_raw,BITMAP_SIZE(slot_all));
            root->delete_slock(lock_raw,BITMAP_SIZE(slot_all));
            // root->delete_items(items_raw,slot_all);
            root->delete_subtree(root_da,1);
            return true;
        }

        void ShowIndexLayer(){
            cout<<"-----ShowIndexLayer-----"<<endl;
            int cur_height = GetMaxHeight();
            SNode *pr = head_;
            for(int i = MaxLevel;i>cur_height;i--){
                pr = reinterpret_cast<Index*>(pr)->Down();
            }
            SNode *cur = pr;
            for(int i = cur_height;i>0;i--){
                int node_cnt = -1;
                SNode *n = cur;
                cout<<"layer "<<i<<":"<<endl;
                while(n->Key != KeyMax){
                    // reinterpret_cast<Index*>(n)->Show();
                    node_cnt++;
                    n = n->Next();
                }
                cout<<"sum up:"<<node_cnt<<std::endl;
                cur = reinterpret_cast<Index*>(cur)->Down();
            }
        }

        int ShowSegmentNumber(const char file_name[],bool write_ = true){
            Segment_pt* head_seg = nullptr;
            SNode* pr_ = head_;
            for(int i = MaxLevel;i>0;i--){
                pr_ = reinterpret_cast<Index*>(pr_)->Down();
            }
            head_seg = reinterpret_cast<Segment_pt*>(pr_);
            int cnt = 0;
            SNode* cur = head_seg->Next();
            while(cur->Key != KeyMax){
                if(write_){
                    Segment_pt *node_seg = reinterpret_cast<Segment_pt*>(cur);
                    auto ESIZE = reinterpret_cast<Segment_pt*>(cur)->DataArray->size.load(std::memory_order_acquire);
                    string kk = to_string(cur->Key)+"\t"+to_string(reinterpret_cast<Segment_pt*>(cur)->bound)+"\t"+to_string(ESIZE)+"\n";
                    // to_string(ESIZE*1.0/(reinterpret_cast<Segment_pt*>(cur)->DataArray->num_items))+"\n";
                    write_into_file(file_name,kk.c_str());
                }
                cnt++;
                cur = cur->Next();
            }
            std::cout<<"SegmentNumber:"<<cnt<<std::endl;
            return cnt;
        }

        void FoldSegment(){
            SNode *x = head_;
            while(x->isIndexNode()){
                x = reinterpret_cast<Index*>(x)->Down();
            }
            x = x->Next();
            Segment_pt *n=nullptr;
            while(x->Key != KeyMax){
                n = reinterpret_cast<Segment_pt*>(x);
                subtree *seg = n->DataArray;
                const int ESIZE = seg->size.load(std::memory_order_acquire);
                if(ESIZE>1){
                    K *keys = new K[ESIZE];
                    V *values = new V[ESIZE];
                    n->scan_and_destroy_subtree(n->DataArray,keys,values,ESIZE);
                    vector<int> after_smo_group_key;
                    // std::pair<subtree*,int> res_ = locate->rebuild_tree(keys,values,ESIZE);
                    std::pair<subtree*,int> res_ = n->rebuild_tree_FCMD(keys,values,ESIZE,after_smo_group_key);
                    if(n->group_key_num){
                        delete[] n->group_key_num;
                    }
                    n->CreateGroupKeyNumArray(after_smo_group_key);
                    delete[] n->group_depth;
                    n->CreateGroupDepth(after_smo_group_key.size());
                    n->SetDataArray(res_.first);
                    n->SetSizeBound();
                    n->UpdateBaseKeyNum(ESIZE);
                    delete[] keys;
                    delete[] values;
                }
                x = x->Next();
            }

        }

        long long SpaceSize(){
            long long space_sum  = 0;
            //skiplist class
            space_sum += sizeof(skiplist);
            SNode *x = head_;
            SNode *pr = x;
            for(int i = MaxLevel;i>0;i--){
                pr = x;
                while(pr){
                    space_sum += reinterpret_cast<Index*>(pr)->SpaceSize();
                    pr = pr->Next();
                }
                x = reinterpret_cast<Index*>(x)->Down();
            }
            cout<<"index layer size:"<<space_sum<<endl;
            pr = x;
            while (pr){
                space_sum += reinterpret_cast<Segment_pt*>(pr)->SpaceSize();
                pr = pr->Next();
            }
            
            return space_sum;
        }

        void ShowKeyDisinSubtree(const char filename[] = "./KeyDis.csv"){
            Segment_pt* head_seg = nullptr;
            SNode* pr_ = head_group[0];
            head_seg = reinterpret_cast<Segment_pt*>(pr_);
            int cnt = 0;
            SNode* cur = head_seg->Next();
            string head_col = "start \t end \t ESIZE \t layer1_cnt\n";
            write_into_file(filename,head_col.c_str());
            while(cur->Key != KeyMax){
                    Segment_pt *node_seg = reinterpret_cast<Segment_pt*>(cur);
                    subtree *DataArray = node_seg->DataArray;
                    int ESIZE = DataArray->size.load(std::memory_order_acquire);
                    int layer1_cnt = 0;
                    for(int i = 0;i<DataArray->num_items;i++){
                        if(BITMAP_GET(DataArray->none_bitmap,i) == 0){
                            if(BITMAP_GET(DataArray->child_bitmap,i) == 0){
                                layer1_cnt++;
                            }
                        }
                    }
                    string kk = to_string(cur->Key)+"\t"+to_string(reinterpret_cast<Segment_pt*>(cur)->bound)+"\t"+to_string(ESIZE)+"\t"+
                    to_string(layer1_cnt)+ "\n";
                    write_into_file(filename,kk.c_str());
                    cur = cur->Next();
                }
        }

        //--------------------------skiplist member variable--------------------------//
        std::atomic<int> max_height_; 
        int MaxLevel;
		int gamma;
        double linearity;
        SNode* head_;
        SNode* tail_;
        vector<SNode*>head_group;
        vector<subtree**> route;
        int work_num;
        skiplist();
        skiplist(int MaxLevel,int gamma,int thread_n):max_height_(0),MaxLevel(MaxLevel),
            gamma(gamma),linearity(LINAERITY),work_num(thread_n){
            /*
            头尾节点 各自有1-Maxlevel的index node，作指示作用
            中间节点，一开始不设置index node，仅有data layer,插入只会发生在split后
            */
            head_group.reserve(MaxLevel+1);
            vector<SNode*> left_index(MaxLevel+1,nullptr);//store the all level SNode of head_
            vector<SNode*> right_index(MaxLevel+1,nullptr);//store the all level SNode of tail_
            head_ = NewIndexBoundArray(MaxLevel,0,0,left_index);
            tail_ = NewIndexBoundArray(MaxLevel,KeyMax,KeyMax,right_index);
            head_group.assign(left_index.begin(),left_index.end());

            SNode *middle_node = NewSegment_pt(1,KeyMax,false);
            {//segment link
                reinterpret_cast<Segment_pt*>(left_index[0])->SetNext(middle_node);
                reinterpret_cast<Segment_pt*>(middle_node)->SetNext(right_index[0]);
            }
            {//index link
                for(int i = 1;i<=MaxLevel;i++){
                    reinterpret_cast<Index*>(left_index[i])->SetNext(right_index[i]);
                }
            }

            route.reserve(work_num);
            for(int i = 0;i<work_num;i++){
                route.push_back((subtree**)malloc(sizeof(subtree*)*MAX_DEPTH*4));
            }
        }
        skiplist(int MaxLevel,int gamma,int thread_n,KeyType domain_min,KeyType domain_max):max_height_(0),
            MaxLevel(MaxLevel),gamma(gamma),linearity(LINAERITY),work_num(thread_n){
            /*
            头尾节点 各自有1-Maxlevel的index node，作指示作用
            中间节点，一开始不设置index node，仅有data layer,插入只会发生在split后
            */
            head_group.reserve(MaxLevel+1);
            vector<SNode*> left_index(MaxLevel+1,nullptr);//store the all level SNode of head_
            vector<SNode*> right_index(MaxLevel+1,nullptr);//store the all level SNode of tail_
            head_ = NewIndexBoundArray(MaxLevel,0,0,left_index);
            tail_ = NewIndexBoundArray(MaxLevel,KeyMax,KeyMax,right_index);
            head_group.assign(left_index.begin(),left_index.end());

            SNode *middle_node = NewSegment_pt(domain_min,domain_max+1,false);
            {//segment link
                reinterpret_cast<Segment_pt*>(left_index[0])->SetNext(middle_node);
                reinterpret_cast<Segment_pt*>(middle_node)->SetNext(right_index[0]);
            }
            {//index link
                for(int i = 1;i<=MaxLevel;i++){
                    reinterpret_cast<Index*>(left_index[i])->SetNext(right_index[i]);
                }
            }

            route.reserve(work_num);
            for(int i = 0;i<work_num;i++){
                route.push_back((subtree**)malloc(sizeof(subtree*)*MAX_DEPTH*4));
            }
        }
        ~skiplist(){
            //TODO
            for(int i = 0;i<work_num;i++){
                free(route[i]);
            }
        }
};

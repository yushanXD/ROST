#include "Conskiplist.hpp"
#include <iostream>
#include <set>

#define PRFO 0
#define PRFOINSERT 0
#define PRFOQUERY 0

#if PRFO
#include<gperftools/profiler.h>
#endif

#define MM 1000000
#define NUMBERDATA (64*MM)
#define PRELOAD (0)
#define THREAD_NUMBER (32)
#define NOFINDDEBUG 0
#define QUERY_TEST 0
#define FOLDKEY 1
#define SPACEPRINT 0
#define SegmentGamma 16

#define STAGE_TEST 0
#define print_statics 0
#define WRITE_ONLY 0

bool DoTestBench = 0;
KeyType *input_data;
bool *input_type;
skiplist<KeyType,VaueType,ModelType> *list = 
    new skiplist<KeyType,VaueType,ModelType>(SkiplistMaxLevel,SegmentGamma,THREAD_NUMBER);

#if print_statics
long long path_sum_t[THREAD_NUMBER];
long long depth_sum_t[THREAD_NUMBER];
long long loop_sum_t[THREAD_NUMBER];
long long rebuild_sum_t[THREAD_NUMBER];
long long skip_sum_t[THREAD_NUMBER];
long long binary_skip_sum_t[THREAD_NUMBER];
#endif

#if STAGE_TEST
#define STAGEcnt 10
#define STAGESIZE (NUMBERDATA / STAGEcnt)
#endif

using namespace chrono;

void GetDataFromText(char path[]){
    input_data = new KeyType[NUMBERDATA];
    #if !WRITE_ONLY
    input_type = new bool[NUMBERDATA];
    #endif
    ifstream myfile(path);
    if (!myfile.is_open())
	{
		cout << "can not open this file" << endl;
		exit(-1);
	}
    for(int i = 0;i<NUMBERDATA;i++){
        myfile >> input_data[i];
        #if !WRITE_ONLY
        myfile >> input_type[i];
        #endif
    }
    myfile.close();
    // std::random_device rd;
    // std::mt19937 g(rd());
    // std::shuffle(input_data, input_data+NUMBERDATA, g);
}

void GenerateData(){
    input_data = new KeyType[NUMBERDATA];
    input_type = new bool[NUMBERDATA];
    std::mt19937_64 rng((unsigned)time(NULL));
    std::uniform_int_distribution<uint64_t> distribution(1, KeyMax);
    std::uniform_int_distribution<int> distribution_2(0, 1);
    for(int i = 0; i < NUMBERDATA;i++ ){
        input_data[i] = distribution(rng);
        input_type[i] = distribution_2(rng);
    }
}

void test_query_optimistic(const int id,const int bound_l,const int bound_r ){
    std::pair<int,VaueType> res;
    int nofind = 0;
    #if print_statics
    long long path_sum = 0,depth_sum = 0,skip_sum = 0,b_skip_sum = 0;
    int path_  = 0, depth_ = 0,skip_ = 0,b_skip_ = 0;
    #endif
    for(int i = bound_l;i<bound_r;i++){
        if(input_data[i] == 0 || input_data[i] == KeyMax)
            continue;
        #if print_statics
        res = list->Lookup_optimistic_debug(id,input_data[i],path_,skip_,depth_,b_skip_);
        path_sum += path_;
        depth_sum += depth_;
        skip_sum += skip_;
        b_skip_sum += b_skip_;
        #else
        res = list->Lookup_optimistic(id,input_data[i]);
        #endif
        if(!(res.first)){
            nofind++;
        }
    }
    #if print_statics
    path_sum_t[id] = path_sum;
    depth_sum_t[id] = depth_sum;
    skip_sum_t[id] = skip_sum;
    binary_skip_sum_t[id] = b_skip_sum;
    #endif
    if(nofind)
        std::cout<<"nofind:\t"<<nofind<<std::endl;
}


#if print_statics
void DoRequest(int id,int stage = 0){
    #if STAGE_TEST
    int key_dis = (STAGESIZE) / THREAD_NUMBER;
    int bound_l = id * (key_dis) + STAGESIZE * stage;
    int bound_r = (id+1)*(key_dis) + STAGESIZE * stage;
    #else
    int key_dis = (NUMBERDATA - PRELOAD) / THREAD_NUMBER;
    int bound_l = id * (key_dis) + PRELOAD;
    int bound_r = (id+1)*(key_dis) + PRELOAD;
    #endif
    int depth_ = 0,path_ = 0,skip_=0;
    int rebuild = 0;
    long long loop_cnt = 0;
    long long sum_rebuild = 0;
    long long sum_depth = 0,sum_path = 0,sum_loop = 0;
    for(int i = bound_l;i<bound_r;i++){
        if(input_data[i] == 0 || input_data[i] == KeyMax)
            continue;
        if(input_type[i] == 1){
            list->Add_debug(id,input_data[i],i,path_,skip_,depth_,loop_cnt,rebuild);
        }else if(input_type[i] == 0){
            // list->Lookup(id,input_data[i]);
            list->Lookup_optimistic(id,input_data[i]);
        }
        
        // list->Add_partial_rebuild_debug(id,input_data[i],i,path_,skip_,depth_,loop_cnt,rebuild);
        // if(list->Lookup_optimistic(id,input_data[i]).first == false){
        //     cout<<"no find"<<endl;
        // }
        sum_depth += depth_;
        sum_path += path_;
        sum_loop += loop_cnt;
        sum_rebuild += rebuild;
    }
    path_sum_t[id] = sum_path;
    depth_sum_t[id] = sum_depth;
    loop_sum_t[id] = sum_loop;
    rebuild_sum_t[id] = sum_rebuild;
}
#else
void DoRequest(int id,int stage = 0){
    #if STAGE_TEST
    int key_dis = (STAGESIZE) / THREAD_NUMBER;
    int bound_l = id * (key_dis) + STAGESIZE * stage;
    int bound_r = (id+1)*(key_dis) + STAGESIZE * stage;
    #else
    int key_dis = (NUMBERDATA - PRELOAD) / THREAD_NUMBER;
    int bound_l = id * (key_dis) + PRELOAD;
    int bound_r = (id+1)*(key_dis) + PRELOAD;
    #endif
    for(int i = bound_l;i<bound_r;i++){
        if(input_data[i] == 0 || input_data[i] == KeyMax)
            continue;
        if(input_type[i] == 1){
            list->Add(id,input_data[i],i);
        }else if(input_type[i] == 0){
            list->Lookup_optimistic(id,input_data[i]);
        }
    }
}
#endif

void Query_exp_optimistic(int &st){
    std::vector<thread> threads_2;
    const auto start_time = std::chrono::steady_clock::now();
    int query_key_dis = NUMBERDATA/THREAD_NUMBER;
    #if PRFOQUERY
    string name = "./profile/query_optimistic.prof";
    ProfilerStart(name.c_str());
    #endif
    for(int idx=0; idx < THREAD_NUMBER; idx++){
        threads_2.push_back(thread(test_query_optimistic, idx,st,st+query_key_dis));
        st+=query_key_dis;
    } 
    for(int idx=0; idx <THREAD_NUMBER; idx++){
        threads_2[idx].join();
    }
    #if PRFOQUERY
    ProfilerStop();
    #endif
    const auto end_time = std::chrono::steady_clock::now();
    const auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time);
    std::cout << "query time: " << duration.count() <<std::endl;
    string k = std::to_string(NUMBERDATA*1.0 / duration.count())+",\n";
    write_into_file("./throughput.csv",k.c_str());
    #if print_statics
    long long path = 0,depth = 0,skips = 0,b_skips = 0;
    for(int j = 0;j<THREAD_NUMBER;j++){
        path += path_sum_t[j];
        depth += depth_sum_t[j];
        skips += skip_sum_t[j];
        b_skips += binary_skip_sum_t[j];
    }
    string outs = "avg path:"+to_string(path*1.0 / NUMBERDATA)+","+
        "avg skips:"+ to_string(skips *1.0 / NUMBERDATA) + ","+
        "avg depth:"+to_string(depth*1.0 / NUMBERDATA)+ ","+
        "avg b skips in ordered array:"+ to_string(b_skips *1.0 / NUMBERDATA) +"\n";
    write_into_file("./throughput.csv",outs.c_str());
    #endif
}

void RangeQuery_Test(){
    // skiplist<KeyType,VaueType,ModelType>::subtree** route = 
    //     (skiplist<KeyType,VaueType,ModelType>::subtree**)malloc(
    //             sizeof(skiplist<KeyType,VaueType,ModelType>::subtree*)*1000);
    for(int i = 0;i<4*MM;i++){
        if(input_data[i] == 0 || input_data[i] == KeyMax)
            continue;
        list->Add(0,input_data[i],i);
    }
    cout<<"insert finish"<<endl;
    vector<std::pair<KeyType,VaueType>> rg_res;
    KeyType st = input_data[0];
    int size_num = 50;
    list->Lookup(0,st,size_num,rg_res);
    for(auto it:rg_res){
        std::cout<<it.first<<","<<it.second<<std::endl;
    }
    
}

void Run(int stage = 0){
    std::vector<thread> threads;
    const auto start_time = std::chrono::steady_clock::now();
    for(int idx=0; idx < THREAD_NUMBER; idx++){
        threads.push_back(thread(DoRequest,idx,stage));
    } 
    for(int idx=0; idx <THREAD_NUMBER; idx++){
        threads[idx].join();
    }

    const auto end_time = std::chrono::steady_clock::now();
    const auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time);
    string outs = "operation time: "+ std::to_string( duration.count()) +"\t";
    std::cout<<outs<<std::endl;
    #if STAGE_TEST
    string k = std::to_string((NUMBERDATA*1.0/STAGEcnt)/duration.count())+",";
    write_into_file("./throughput.csv",k.c_str());
    #if !print_statics
    if(stage == STAGEcnt-1){
        write_into_file("./throughput.csv","\n");
    }
    #endif
    #else
    string k = std::to_string((NUMBERDATA*1.0)/duration.count())+",";
    write_into_file("./throughput.csv",k.c_str());
    #endif
    
}

void pre_insert(int id){
    int key_dis = PRELOAD / THREAD_NUMBER;
    int bound_l = id * (key_dis);
    int bound_r = (id+1)*(key_dis);
    // skiplist<KeyType,VaueType,ModelType>::subtree** route = (skiplist<KeyType,VaueType,ModelType>::subtree**)malloc(sizeof(skiplist<KeyType,VaueType,ModelType>::subtree*)*MAX_DEPTH*4);
    for(int i = bound_l;i<bound_r;i++){
        if(input_data[i] == 0 || input_data[i] == KeyMax)
            continue;
        list->Add(id,input_data[i],i);
    }
    // free(route);
}

void TestBench(){
    #if STAGE_TEST
    for(int i = 0;i<STAGEcnt;i++){
        #if CLOCK_MARK
        for(int i = 0;i<32;i++){
            rebuild_time[i] = 0;
        }
        #endif
        cout<<"stage "<<i<<endl;
        #if PRFOINSERT
        string name = "./"+to_string(i)+".prof";
        ProfilerStart(name.c_str());
        #endif
        Run(i);
        #if PRFOINSERT
        ProfilerStop();
        #endif
        int seg_num = list->ShowSegmentNumber("./segment.csv",false);
        #if print_statics
        long long path = 0,depth = 0,loop_cnt = 0,rebuild_cnt = 0;
        for(int j = 0;j<THREAD_NUMBER;j++){
            path += path_sum_t[j];
            depth += depth_sum_t[j];
            loop_cnt += loop_sum_t[j];
            rebuild_cnt += rebuild_sum_t[j];
        }
        string outs = "avg path:"+to_string(path*1.0 / STAGESIZE)+
            ",avg depth:"+to_string(depth*1.0 / STAGESIZE)+
            ",avg loop cnt:"+to_string(loop_cnt*1.0 / STAGESIZE)+
            ",rebuild cnt:"+to_string(rebuild_cnt)+
            ",segment number:"+to_string(seg_num)+"\n";
        write_into_file("./throughput.csv",outs.c_str());
        #if CLOCK_MARK
        for(int i = 0;i<32;i++){
            cout<<i<<" thread "<<" smo : "<<(rebuild_time[i])<<endl;
        }
        cout<<endl;
        #endif
        #endif
    }

    #else
    #if CLOCK_MARK
    for(int i = 0;i<32;i++){
        rebuild_time[i] = 0;
    }
    #endif
    #if PRFOINSERT
        string name = "./pprof_total.prof";
        ProfilerStart(name.c_str());
    #endif

    Run();
    
    #if PRFOINSERT
    ProfilerStop();
    #endif

    int seg_num = list->ShowSegmentNumber("./segment.csv",false);
    #if print_statics
        long long path = 0,depth = 0,loop_cnt = 0,rebuild_cnt = 0;
        for(int j = 0;j<THREAD_NUMBER;j++){
            path += path_sum_t[j];
            depth += depth_sum_t[j];
            loop_cnt += loop_sum_t[j];
            rebuild_cnt += rebuild_sum_t[j];
        }
        string outs = "avg path:"+to_string(path*1.0 / NUMBERDATA)+
            ",avg depth:"+to_string(depth*1.0 / NUMBERDATA)+
            ",avg loop cnt:"+to_string(loop_cnt*1.0 / NUMBERDATA)+
            ",rebuild cnt:"+to_string(rebuild_cnt)+
            ",segment number:"+to_string(seg_num)+"\n";
        write_into_file("./throughput.csv",outs.c_str());
        #if CLOCK_MARK
        for(int i = 0;i<32;i++){
            cout<<i<<" thread "<<" smo : "<<(rebuild_time[i])<<endl;
        }
        #endif
    #endif
    
    #endif
    list->ShowIndexLayer();
    
    #if QUERY_TEST
    int n = 0;
    cout<<endl<<"-----Query_exp_optimistic-----"<<endl;
    Query_exp_optimistic(n);
    #endif
    
    #if FOLDKEY
    list->FoldSegment();
    #endif
    
    #if SPACEPRINT
    string outs = std::to_string(list->SpaceSize())+"\n";
    write_into_file("./space_size.txt",outs.c_str());
    #endif
}

int main(int argc, char *argv[]){
    srand((int)time(0));
    std::cout<<"NUMBERDATA:"<<NUMBERDATA<<"\tTHREAD_NUMBER:"<<THREAD_NUMBER<<std::endl;
    std::cout<<"SkiplistMaxLevel:"<<SkiplistMaxLevel<<"\tmax segment size:"<<SEGMENT_MAX_SIZE<<std::endl
        <<"MAX_DEPTH:"<<MAX_DEPTH<<"\tIndexGamma:"<<Gm<<std::endl
        <<"MERGE_THRESHOLD:"<<MERGE_THRESHOLD<<"\tITEM_GROUP_SIZE:"<<ITEM_GROUP_SIZE<<endl;

    rcu_init(THREAD_NUMBER);
    if(argc == 1 && !DoTestBench){
        list->Add(0,5,5);
        auto res = list->Lookup_optimistic(0,5);
        if(res.first == false){
            cout<<"key is not in rost"<<endl;
        }
    }else{
        cout<<"loading...";
        if(argc == 1){
            GenerateData();
        }else{
            cout<<argv[1]<<std::endl;
            GetDataFromText(argv[1]);
        }
        cout<<"load finish"<<endl;
        TestBench();
    }
}
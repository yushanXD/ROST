#include<iostream>
#include<cmath>


inline double getThdUtil(double thds)
{
    return 1.0825 - 0.22079752*log(thds);
}

//return value:  k - number of splits; k = 1 no split;  k > 1 split the segment into k subsegments  
//parameter: thread number m, max_height h
int getSplitK(double m, double h)
{
   double k = 0;
   double max_u = 0;
   double max_k = 0;
   for(k = 1; k <=2*m; k+=2) 
   {
        // std::cout<<"k: "<<k<<std::endl;
        // std::cout<<getThdUtil(m)<<std::endl;
        double u1 = (h*3/4) * getThdUtil(m/k);
        double u2 = ((h/k+h)/2 + log2(k)) * getThdUtil(m);
        double u = u1/u2;
        // std::cout<<"u1: "<<u1<<" u2: "<<u2<<std::endl;
        // std::cout<<"util: "<< u<<std::endl;
        if(u > max_u)
        {
            max_u = u;
            max_k = k;
        }
   }
  //  std::cout<<"max_u: " <<max_u<<" ";
   if (max_u > 1)
      return max_k;
    else
      return 1;
}
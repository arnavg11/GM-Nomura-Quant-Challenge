#include <exception>
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <float.h>
#include <cassert>
using namespace std;
#define C_MAX 3
#define C_MIN -3
#define INF DBL_MAX/10
#define N_POINTS 2000
#define BINARY_SEARCH_PRECISION .000001
const double PI = 3.141;
double integrateBinomial (double end,double start,function<double(double)>f,double variance)
{
    double ret=0;
    double del = (C_MAX-C_MIN);
    del/=N_POINTS;
    for(double z1 = start; z1<end; z1+=del){
        ret+=f(z1+del/2)*exp(-pow((z1+del/2),2)/2/variance)*del/sqrt(2*PI*variance);
    }
    return ret;
}
double integrateBinomialFast(double end,double start,function<double(double)>f,int variance)
{
    return (0.5 * erfc(-end/sqrt(variance) * M_SQRT1_2)- 0.5 * erfc(-start/sqrt(variance) * M_SQRT1_2))*f((end+start)/2);
}

class ValueNote{
private:
    double notational,maturity,valueRate,paymentFrequency;
public:
    ValueNote():notational(100),maturity(1),valueRate(0), paymentFrequency(1){}
    ValueNote(int _notational, double _maturity, double _valueRate, double _paymentFreq):notational(_notational),maturity(_maturity),valueRate(_valueRate), paymentFrequency(_paymentFreq){
        assert(_notational>0);
        assert(_maturity>0);
        assert(_valueRate>=0);
        assert(_paymentFreq>0);
    }
    double getPriceLinear(double rate)const{
        return notational*(1-rate*maturity/100);
    }
    double getRateLinear(double price)const{
        return (1-price/notational)*100/maturity;
    }
    double getSinglePriceSensitivityLinear()const{
        return -notational*maturity/100;
    }
    double getDoublePriceSensitivityLinear()const{
        return 0;
    }
    double getSingleRateSensitivityLinear()const{
        return -100/notational/maturity;
    }
    double getDoubleRateSensitivityLinear()const{
        return 0;
    }
    //function overriding to match pattern of similar functions
    double getSinglePriceSensitivityLinear(double rate)const{
        return -notational*maturity/100;
    }
    double getDoublePriceSensitivityLinear(double rate)const{
        return 0;
    }
    double getSingleRateSensitivityLinear(double price)const{
        return -100/notational/maturity;
    }
    double getDoubleRateSensitivityLinear(double price)const{
        return 0;
    }
    
    double getPriceCumulative(double rate)const{
        double f = 1+rate/100/paymentFrequency;
        double n = maturity*paymentFrequency;
        return valueRate*notational*(1-pow(f,-(n+1)))/rate+notational/pow(f, n);
    }
    double getRateCumulative(double price)const{
        //binary searches across all valid values of rates
        double l = 0,r = 100/maturity;
        while(r-l>BINARY_SEARCH_PRECISION){
            double m = (l+r)/2;
            if(getPriceCumulative(m)>price){
                l=m;
            }else r = m;
        }
        return (l+r)/2;
    }
    double getSinglePriceSensitivityCumulative(double rate)const{
        double t = pow((1+rate/100/paymentFrequency),maturity*paymentFrequency+1);
        double n = maturity/paymentFrequency;
        double ret = -valueRate*notational/rate/rate;
        ret+=valueRate*notational/rate/t*(1/rate+(n+1)/(100*paymentFrequency+rate));
        ret-=notational*maturity/100/t;
        return ret;
    }
    double getDoublePriceSensitivityCumulative(double rate)const{
        double rpf = 1+rate/100/paymentFrequency,mpf = maturity*paymentFrequency;
        double ermpf = pow(rpf,mpf);
        double ret = 2*valueRate*notational/pow(rate,3);
        double f1 = valueRate*notational/pow(rate*ermpf*rpf,2)*(ermpf*rpf+(mpf+1)*rate*ermpf/100/paymentFrequency);
        ret-=f1*(1/rate+(mpf+1)/(100*paymentFrequency+rate));
        ret-=valueRate*notational/rate/ermpf/rpf*(1/rate/rate+(mpf+1)/pow(100*paymentFrequency+rate,2));
        ret+=notational*maturity*(mpf+1)/10000/paymentFrequency/ermpf/pow(rpf,2);
        return ret;
    }
    double getSingleRateSensitivityCumulative(double price)const{
        return 1/getSinglePriceSensitivityCumulative(getRateCumulative(price));
    }
    double getDoubleRateSensitivityCumulative(double price)const{
        double rate = getRateCumulative(price);
        return -getDoublePriceSensitivityCumulative(rate)/pow(getSinglePriceSensitivityCumulative(rate),3);
    }
    
    double getPriceRecursive(double rate)const{
        double n = maturity/paymentFrequency;
        double fv = 0;
        const double vf = valueRate*notational/100/paymentFrequency;
        double f = 1+rate/paymentFrequency/100;
        for(int i = 0; i<n-1;i++)fv = (fv+vf)*f;
        fv+=vf;     //nth iteration requires m_n to be 0
        return (notational+fv)/(1+rate*maturity/100);
    }
    double getRateRecursive(double price)const{
        //binary searches across all valid values of rates
        double l = 0,r = 100/maturity;
        while(r-l>BINARY_SEARCH_PRECISION){
            double m = (l+r)/2;
            if(getPriceRecursive(m)>price){
                l=m;
            }else r = m;
        }
        return (l+r)/2;
    }
    double getSinglePriceSensitivityRecursive(double rate)const{
        //starts from fv1
        double n = maturity/paymentFrequency;
        const double vf = valueRate*notational/100/paymentFrequency,M_i =1/paymentFrequency, f = 1+rate/paymentFrequency/100,rpf = 1+rate/100/paymentFrequency;
        double fv = vf*f,fv_ = vf/100/paymentFrequency;      //fv_ stores derivative of fv
        for(int i = 0; i<n-2;i++){
            double fvPrev = fv;
            fv = (fv+vf)*f;
            fv_ = M_i*fv/100/rpf+fv_*rpf;
        }
        //since M_n=0 fv_remains same,
        fv+=vf;
        return (fv_*(1+rate*maturity/100)+maturity*fv/100)/pow((1+rate*maturity/100),2);
    }
    double getDoublePriceSensitivityRecursive(double rate)const{
        double n = maturity/paymentFrequency;
        const double vf = valueRate*notational/100/paymentFrequency,M_i =1/paymentFrequency, f = 1+rate/paymentFrequency/100,rpf = 1+rate/100/paymentFrequency;
        double fv = vf*f,fv_ = vf/100/paymentFrequency,fv__ = 0;      //fv_ stores derivative of fv and fv__ stores second derivative of fv
        for(int i = 0; i<n-2;i++){
            double fvPrev = fv,fv_prev = fv_;
            fv = (fv+vf)*f;
            fv_ = M_i*fv/100/rpf+fv_*rpf;
            fv__ = 2*fv_prev/100/paymentFrequency+fv__*rpf;
        }
        //since M_n=0 fv_remains same,
        fv+=vf;
        return fv__/rpf-fv*2*pow(maturity,2)/10000/pow(rpf,3);
    }
    double getSingleRateSensitivityRecursive(double price)const{
        return 1/getSinglePriceSensitivityRecursive(getRateRecursive(price));
    }
    double getDoubleRateSensitivityRecursive(double price)const{
        double rate = getRateRecursive(price);
        return -getDoublePriceSensitivityRecursive(rate)/pow(getSinglePriceSensitivityRecursive(rate),3);
    }
    double getVF()const{
        return valueRate*notational/100/paymentFrequency;
    }
    double getValueRate()const{
        return valueRate;
    }
};
struct BasketElement{
    ValueNote v;
    double volatility;
};
class DeliveryContract{
private:
    double SVR,expirationTime, riskFreeIntRate;
    vector<BasketElement> basket;
public:
    DeliveryContract():SVR(.1),expirationTime(1),riskFreeIntRate(.1),basket(vector<BasketElement>()){}
    DeliveryContract(double SVR_,double expirationTime_,double riskFreeIntRate_){
        assert(SVR_>0);
        assert(expirationTime_>0);
        assert(riskFreeIntRate_>0);
        riskFreeIntRate = riskFreeIntRate_;
        SVR = SVR_;
        expirationTime = expirationTime_;
    }
    
    double getRelativeFactor(ValueNote& v)const{
        //returns relative cumulative factor
        return v.getPriceCumulative(SVR)/100;
        
    }
    void addValueNote(ValueNote& v, double volatility){
        assert(volatility>=0);
        BasketElement b;b.v = v;b.volatility = volatility;
        basket.emplace_back(b);
    }
    double getEffectiveRate(BasketElement& b,double Wt)const{
        double VPted =(1+riskFreeIntRate*expirationTime)*(b.v.getPriceCumulative(b.v.getValueRate())-b.v.getVF()/(1+riskFreeIntRate*expirationTime));
        double er_ted = b.v.getPriceCumulative(VPted);
        //calculating risk adjust effective rate
        double A = .5*b.v.getDoublePriceSensitivityCumulative(er_ted)*exp(pow(b.volatility,2)*expirationTime);
        double B = b.v.getSinglePriceSensitivityCumulative(er_ted)-b.v.getDoublePriceSensitivityCumulative(er_ted)*er_ted;
        double C = .5*b.v.getDoublePriceSensitivityCumulative(er_ted)*pow(er_ted,2) -b.v.getSinglePriceSensitivityCumulative(er_ted)*er_ted;
        double ER_t = (-B+sqrt(B*B-4*A*C))/2/A;
        
        double ERT = ER_t*exp(b.volatility*Wt-expirationTime*pow(b.volatility,2)/2);
        return ERT;
    }
    static void solve_linear_3x3(const double A[3][3], const double B[3], double& x0, double& x1, double& x2) {
        double detA =
            A[0][0]*(A[1][1]*A[2][2] - A[1][2]*A[2][1]) -
            A[0][1]*(A[1][0]*A[2][2] - A[1][2]*A[2][0]) +
            A[0][2]*(A[1][0]*A[2][1] - A[1][1]*A[2][0]);

        assert(std::abs(detA) > 1e-12); // Make sure determinant isn't too small

        // Dx
        double Dx =
            B[0]*(A[1][1]*A[2][2] - A[1][2]*A[2][1]) -
            A[0][1]*(B[1]*A[2][2] - A[1][2]*B[2]) +
            A[0][2]*(B[1]*A[2][1] - A[1][1]*B[2]);

        // Dy
        double Dy =
            A[0][0]*(B[1]*A[2][2] - A[1][2]*B[2]) -
            B[0]*(A[1][0]*A[2][2] - A[1][2]*A[2][0]) +
            A[0][2]*(A[1][0]*B[2] - B[1]*A[2][0]);

        // Dz
        double Dz =
            A[0][0]*(A[1][1]*B[2] - B[1]*A[2][1]) -
            A[0][1]*(A[1][0]*B[2] - B[1]*A[2][0]) +
            B[0]*(A[1][0]*A[2][1] - A[1][1]*A[2][0]);

        x0 = Dx / detA;
        x1 = Dy / detA;
        x2 = Dz / detA;
    }

    static void weightedQuadraticFit(vector<double>& z_vals,vector<double>& y_vals,vector<double>& weights,double& a, double& b, double& c){
        assert(z_vals.size() == y_vals.size() && y_vals.size() == weights.size());

        double A[3][3] = {0};
        double B[3] = {0};

        for (size_t i = 0; i < z_vals.size(); ++i) {
            double w = weights[i];
            double z = z_vals[i];
            double y = y_vals[i];

            double z2 = z * z;
            double z3 = z2 * z;
            double z4 = z3 * z;

            A[0][0] += w * z4;
            A[0][1] += w * z3;
            A[0][2] += w * z2;
            A[1][1] += w * z2;
            A[1][2] += w * z;
            A[2][2] += w;

            B[0] += w * y * z2;
            B[1] += w * y * z;
            B[2] += w * y;
        }

        // Fill symmetric parts
        A[1][0] = A[0][1];
        A[2][0] = A[0][2];
        A[2][1] = A[1][2];

        solve_linear_3x3(A, B, a, b, c);
    }
    
    void computeQuadraticCoefficients(BasketElement& b,double& a_out, double& b_out, double& c_out)const{
            vector<double> z_vals(N_POINTS);
            vector<double> y_vals(N_POINTS);
            vector<double> weights(N_POINTS);
            double dz = (C_MAX - C_MIN) / (N_POINTS - 1);
            for (int i = 0; i < N_POINTS; ++i) {
                double z = C_MIN + i * dz;
                double weight = exp(-0.5 * z * z) / sqrt(2.0 * PI);//using normal distribution
                double ER_T = getEffectiveRate(b, z);
                double VP = b.v.getPriceRecursive(ER_T);
                double ratio = VP / getRelativeFactor(b.v);

                z_vals[i] = z;
                y_vals[i] = ratio;
                weights[i] = weight;
            }

            weightedQuadraticFit(z_vals, y_vals, weights, a_out, b_out, c_out);
    }
    
    
    
    double getContractPrice(){
        vector<pair<double,pair<int,int>>> intersections;
        vector<vector<double>>coeffs(basket.size(),vector<double>(3,0));
        for(int i = 0;i<basket.size();i++){
            computeQuadraticCoefficients(basket[i], coeffs[i][0], coeffs[i][1], coeffs[i][2]);
        }
        for(int i = 0;i<basket.size();i++)for(int j = 0;j<i;j++){
            double A = coeffs[i][0]-coeffs[j][0],B = coeffs[i][1]-coeffs[j][1],C = coeffs[i][2]-coeffs[j][2];
            if(B*B-4*A*C>0){
                double pt1 = (-B+sqrt(B*B-4*A*C))/2/A;
                double pt2 = (-B-sqrt(B*B-4*A*C))/2/A;
                if(pt1<C_MAX and pt1>C_MIN)intersections.emplace_back(pair<double,pair<int,int>>(pt1,pair<int,int>(i,j)));
                if(pt2<C_MAX and pt2>C_MIN)intersections.emplace_back(pair<double,pair<int,int>>(pt2,pair<int,int>(i,j)));
            }
            sort(intersections.begin(),intersections.end());
        }
        intersections.emplace_back(pair<double,pair<int,int>>(C_MAX,pair<int,int>(-1,-1)));//for last interval
//        vector<double>returnVal(basket.size(),0);
        pair<double,int>curr(INF,-1);           //curr.second stores index most economical ValueNote
        for(int i = 0;i<basket.size();i++){
            int Z =(intersections[0].first+C_MIN)/2;
            double t = coeffs[i][0]*Z*Z+coeffs[i][1]*Z+coeffs[i][2];
            if(t<curr.first)curr = pair<double, int>(t,i);
        }
//        returnVal[curr.second]+=intersections[0].first-C_MIN;
        double Z1 = C_MIN, Z2 = intersections[0].first;double Z = (Z1+Z2)/2;
        double ret =
        integrateBinomial(Z2,Z1,[&](int Z){return basket[curr.second].v.getPriceCumulative(getEffectiveRate(basket[curr.second], Z))/getRelativeFactor(basket[curr.second].v);},sqrt(expirationTime));
        for(int i = 0;i<intersections.size()-1;i++){
            if(curr.second!=intersections[i].second.first and curr.second!=intersections[i].second.second)continue;
            Z1 = intersections[i].first; Z2 = intersections[i+1].first;
            int other = intersections[i].second.first+intersections[i].second.second - curr.second;
            Z =(intersections[i].first+intersections[i+1].first)/2;
            double t1 = basket[curr.second].v.getPriceCumulative(getEffectiveRate(basket[curr.second], Z))/getRelativeFactor(basket[curr.second].v);
            double t2 = basket[other].v.getPriceCumulative(getEffectiveRate(basket[other], Z))/getRelativeFactor(basket[other].v);
            if(t1>t2)curr.second = other;
//            returnVal[curr.second]+=intersections[i+1].first-intersections[i].first;
            ret += integrateBinomial(Z2,Z1,[&](int Z){return basket[curr.second].v.getPriceCumulative(getEffectiveRate(basket[curr.second], Z))/getRelativeFactor(basket[curr.second].v);},sqrt(expirationTime));
        }
        return ret;
    }
    double getContractPriceAccurate(){
//        vector<double>returnVal(basket.size(),0);
        double ret =0,del = ((double)(C_MAX-C_MIN))/N_POINTS;
        
        for(double z = C_MIN;z<C_MAX;z+=del){
            pair<double,int>curr(INF,-1);           //curr.second stores index most economical ValueNote
            for(int i = 0;i<basket.size();i++){
                double t = basket[i].v.getPriceCumulative(getEffectiveRate(basket[i], z+del/2))/getRelativeFactor(basket[i].v);
                if(t<curr.first)curr = pair<double, int>(t,i);
            }
//            returnVal[curr.second]+=intersections[i+1].first-intersections[i].first;
            ret += exp(-pow((z+del/2),2)/2/expirationTime)*del/sqrt(2*PI*expirationTime)*curr.first;
        }
        return ret;
    }
    vector<double> getDeliveryProbabilities(){
        vector<pair<double,pair<int,int>>> intersections;
        vector<vector<double>>coeffs(basket.size(),vector<double>(3,0));
        for(int i = 0;i<basket.size();i++){
            computeQuadraticCoefficients(basket[i], coeffs[i][0], coeffs[i][1], coeffs[i][2]);
        }
        for(int i = 0;i<basket.size();i++)for(int j = 0;j<i;j++){
            double A = coeffs[i][0]-coeffs[j][0],B = coeffs[i][1]-coeffs[j][1],C = coeffs[i][2]-coeffs[j][2];
            if(B*B-4*A*C>0){
                double pt1 = (-B+sqrt(B*B-4*A*C))/2/A;
                double pt2 = (-B-sqrt(B*B-4*A*C))/2/A;
                if(pt1<C_MAX and pt1>C_MIN)intersections.emplace_back(pair<double,pair<int,int>>(pt1,pair<int,int>(i,j)));
                if(pt2<C_MAX and pt2>C_MIN)intersections.emplace_back(pair<double,pair<int,int>>(pt2,pair<int,int>(i,j)));
            }
            sort(intersections.begin(),intersections.end());
        }
        intersections.emplace_back(pair<double,pair<int,int>>(C_MAX,pair<int,int>(-1,-1)));//for last interval
        vector<double>probs(basket.size(),0);
        pair<double,int>curr(INF,-1);           //curr.second stores index most economical ValueNote
        for(int i = 0;i<basket.size();i++){
            int Z =(intersections[0].first+C_MIN)/2;
            double t = coeffs[i][0]*Z*Z+coeffs[i][1]*Z+coeffs[i][2];
            if(t<curr.first)curr = pair<double, int>(t,i);
        }
        double Z1 = C_MIN, Z2 = intersections[0].first;double Z = (Z1+Z2)/2;
        probs[curr.second]+=integrateBinomial(Z2, Z1, [](int z){return 1;},sqrt(expirationTime));
        for(int i = 0;i<intersections.size()-1;i++){
            if(curr.second!=intersections[i].second.first and curr.second!=intersections[i].second.second)continue;
            Z1 = intersections[i].first; Z2 = intersections[i+1].first;
            int other = intersections[i].second.first+intersections[i].second.second - curr.second;
            Z =(intersections[i].first+intersections[i+1].first)/2;
            double t1 = coeffs[curr.second][0]*Z*Z+coeffs[curr.second][1]*Z+coeffs[curr.second][2];
            double t2 = coeffs[other][0]*Z*Z+coeffs[other][1]*Z+coeffs[other][2];
            if(t1>t2)curr.second = other;
            probs[curr.second]+=integrateBinomial(Z2, Z1, [](int z){return 1;},sqrt(expirationTime));
        }
        return probs;
    }
    vector<double> getDeliveryProbabilitiesAccurate(){
        vector<double>returnVal(basket.size(),0);
//        double ret =0;
        double del = ((double)(C_MAX-C_MIN))/N_POINTS;
        
        for(double z = C_MIN;z<C_MAX;z+=del){
            pair<double,int>curr(INF,-1);           //curr.second stores index most economical ValueNote
            for(int i = 0;i<basket.size();i++){
                double t = basket[i].v.getPriceCumulative(getEffectiveRate(basket[i], z+del/2))/getRelativeFactor(basket[i].v);
                if(t<curr.first)curr = pair<double, int>(t,i);
            }
//            returnVal[curr.second]+=intersections[i+1].first-intersections[i].first;
            if(z>-.1){
                double f=exp(-pow((z+del/2)/expirationTime,2)/2)*del/sqrt(2*PI*expirationTime);
            }
            returnVal[curr.second] += exp(-pow((z+del/2),2)/2/expirationTime)*del/sqrt(2*PI*expirationTime);
        }
        return returnVal;
    }
    double getPriceSensitivity(int element, double volatility){
        const int prev = basket[element].volatility;
        basket[element].volatility = volatility;
        vector<pair<double,pair<int,int>>> intersections;
        vector<vector<double>>coeffs(basket.size(),vector<double>(3,0));
        for(int i = 0;i<basket.size();i++){
            computeQuadraticCoefficients(basket[i], coeffs[i][0], coeffs[i][1], coeffs[i][2]);
        }
        for(int i = 0;i<basket.size();i++)for(int j = 0;j<i;j++){
            double A = coeffs[i][0]-coeffs[j][0],B = coeffs[i][1]-coeffs[j][1],C = coeffs[i][2]-coeffs[j][2];
            if(B*B-4*A*C>0){
                double pt1 = (-B+sqrt(B*B-4*A*C))/2/A;
                double pt2 = (-B-sqrt(B*B-4*A*C))/2/A;
                if(pt1<C_MAX and pt1>C_MIN)intersections.emplace_back(pair<double,pair<int,int>>(pt1,pair<int,int>(i,j)));
                if(pt2<C_MAX and pt2>C_MIN)intersections.emplace_back(pair<double,pair<int,int>>(pt2,pair<int,int>(i,j)));
            }
            sort(intersections.begin(),intersections.end());
        }
        intersections.emplace_back(pair<double,pair<int,int>>(C_MAX,pair<int,int>(-1,-1)));//for last interval
//        vector<double>returnVal(basket.size(),0);
        pair<double,int>curr(INF,-1);           //curr.second stores index most economical ValueNote
        for(int i = 0;i<basket.size();i++){
            int Z =(intersections[0].first+C_MIN)/2;
            double t = coeffs[i][0]*Z*Z+coeffs[i][1]*Z+coeffs[i][2];
            if(t<curr.first)curr = pair<double, int>(t,i);
        }
//        returnVal[curr.second]+=intersections[0].first-C_MIN;
        double Z1 = C_MIN, Z2 = intersections[0].first;double Z = (Z1+Z2)/2;
        double ret =0;
        if(curr.second==element)
            ret+=integrateBinomial(Z2, Z1, [&](int Z){
                return (basket[curr.second].v.getSinglePriceSensitivityCumulative(getEffectiveRate(basket[curr.second], Z))/getRelativeFactor(basket[curr.second].v))*(Z-expirationTime*volatility);
            },sqrt(expirationTime));
        for(int i = 0;i<intersections.size()-1;i++){
            if(curr.second!=intersections[i].second.first and curr.second!=intersections[i].second.second)continue;
            Z1 = intersections[i].first; Z2 = intersections[i+1].first;
            int other = intersections[i].second.first+intersections[i].second.second - curr.second;
            Z =(intersections[i].first+intersections[i+1].first)/2;
            double t1 = coeffs[curr.second][0]*Z*Z+coeffs[curr.second][1]*Z+coeffs[curr.second][2];
            double t2 = coeffs[other][0]*Z*Z+coeffs[other][1]*Z+coeffs[other][2];
            if(t1>t2)curr.second = other;
//            returnVal[curr.second]+=intersections[i+1].first-intersections[i].first;
            if(curr.second==element)ret+=integrateBinomial(Z2, Z1, [&](int Z){
                return (basket[curr.second].v.getSinglePriceSensitivityCumulative(getEffectiveRate(basket[curr.second], Z))/getRelativeFactor(basket[curr.second].v))*(Z-expirationTime*volatility);
            },sqrt(expirationTime));
        }
        basket[element].volatility = prev;
        return ret;
    }
    double getPriceSensitivityAccurate(int element, double volatility){
        const int prev = basket[element].volatility;
        basket[element].volatility = volatility;
        double ret =0,del = ((double)(C_MAX-C_MIN))/N_POINTS;
        
        for(double z = C_MIN;z<C_MAX;z+=del){
            pair<double,int>curr(INF,-1);           //curr.second stores index most economical ValueNote
            for(int i = 0;i<basket.size();i++){
                double t = basket[i].v.getPriceCumulative(getEffectiveRate(basket[i], z+del/2))/getRelativeFactor(basket[i].v);
                if(t<curr.first)curr = pair<double, int>(t,i);
            }
//            returnVal[curr.second]+=intersections[i+1].first-intersections[i].first;
            if(curr.second==element)ret += exp(-pow((z+del/2),2)/2/expirationTime)*del/sqrt(2*PI*expirationTime)*(basket[curr.second].v.getSinglePriceSensitivityCumulative(getEffectiveRate(basket[curr.second], z+del/2))/getRelativeFactor(basket[curr.second].v))*(z+del/2-expirationTime*volatility);
        }
        basket[element].volatility = prev;
        return ret;
    }
};

signed main(){
//    freopen("/Users/agupta/Desktop/q/adventOfCode/adventOfCode/output.csv", "w", stdout);
    ValueNote VN1(100, 5, .035, 1);
    ValueNote VN2(100, 1.5, .02, 2);
    ValueNote VN3(100, 4.5, .0325, 1);
    ValueNote VN4(100, 10, .08, 4);
    DeliveryContract d(.05, .25,.04);
    d.addValueNote(VN1,.015);
    d.addValueNote(VN2,.025);
    d.addValueNote(VN3,.015);
    d.addValueNote(VN4,.05);
    auto prob = d.getDeliveryProbabilitiesAccurate();
    
    //code to check the quadraticfitter
//    double a,b,c;
//    vector<double>z = {0,1,2,3,4,5,6};
//    vector<double>y = {1,4,9,16,25,36,49};
//    vector<double>weights = {1,1,1,1,1,1,1};
//    d.weightedQuadraticFit(z, y, weights, a, b, c);
    
    cout<<",Linear ,Cumulative,Recursive,Q 2.1,Q 2.2,Q 2.3,Q 2.4 a),Q 2.4 b)\n";
    cout<<"1.1 a),"<<VN1.getPriceLinear(.05)<<","<<VN1.getPriceCumulative(.05)<<","<<VN1.getPriceRecursive(.05)<<","<<d.getRelativeFactor(VN1)<<","<<d.getContractPriceAccurate()<<","<<prob[0]<<","<<d.getPriceSensitivityAccurate(0, .02)<<",\n";
    cout<<"1.1 b),"<<VN1.getRateLinear(100)<<","<<VN1.getRateCumulative(100)<<","<<VN1.getRateRecursive(100)<<","<<d.getRelativeFactor(VN2)<<",,"<<prob[1]<<","<<d.getPriceSensitivityAccurate(1, .03)<<",\n";
    cout<<"1.2 a),"<<VN1.getSinglePriceSensitivityLinear(.05)<<","<<VN1.getSinglePriceSensitivityCumulative(.05)<<","<<VN1.getSinglePriceSensitivityRecursive(.05)<<","<<d.getRelativeFactor(VN3)<<",,"<<prob[2]<<","<<d.getPriceSensitivityAccurate(2, .04)<<",\n";
    cout<<"1.2 b),"<<VN1.getSingleRateSensitivityLinear(100)<<","<<VN1.getSingleRateSensitivityCumulative(100)<<","<<VN1.getSingleRateSensitivityRecursive(100)<<","<<d.getRelativeFactor(VN4)<<",,"<<prob[3]<<","<<d.getPriceSensitivityAccurate(3, .05)<<",\n";
    cout<<"1.3 a),"<<VN1.getDoublePriceSensitivityLinear(.05)<<","<<VN1.getDoublePriceSensitivityCumulative(.05)<<","<<VN1.getDoublePriceSensitivityRecursive(.05)<<",,,,,\n";
    cout<<"1.3 b),"<<VN1.getDoubleRateSensitivityLinear(100)<<","<<VN1.getDoubleRateSensitivityCumulative(100)<<","<<VN1.getDoubleRateSensitivityRecursive(100)<<",,,,,\n";
}

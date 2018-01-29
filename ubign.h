#include<cstring>
#include<cmath>
#include<cassert>
#include<complex>
#include<vector>
#include<iostream>
#include<iomanip>
#include<type_traits>

using namespace std;

#define FFT_LEN 131072
#ifndef M_PI
const double M_PI = acos(-1);
#endif

vector<complex<double>> fft(const vector<complex<double>> &x, const int &inv){
    static bool fft_ready = false;
    static complex<double> loli[FFT_LEN];
    int n = x.size();
    assert((n&-n)==n && n<=FFT_LEN && abs(inv)==1);
    if(!fft_ready){
        for(int k=0; k<FFT_LEN; k++){
            loli[k] = exp(complex<double>(0, 2*M_PI*k/FFT_LEN));
        }
        fft_ready = true;
    }
    vector<complex<double>> X = x;
    for(int i=1, j=0; i<n; i++){
        for(int k=n>>1; !((j^=k)&k); k>>=1);
        if(i < j){
            swap(X[i], X[j]);
        }
    }
    for(int i=2; i<=n; i*=2){
        int d = (inv==1)? FFT_LEN-(FFT_LEN/i): FFT_LEN/i;
        for(int j=0; j<n; j+=i){
            for(int k=0, a=0; k<i/2; k++, a=(a+d)%FFT_LEN){
                complex<double> s = X[j+k], t = loli[a] * X[j+k+i/2];
                X[j+k] = s + t;
                X[j+k+i/2] = s - t;
            }
        }
    }
    if(inv == -1){
        for(int i=0; i<(int)X.size(); i++){
            X[i] /= n;
        }
    }
    return X;
}

typedef long long ll;
typedef unsigned long long ull;
static const ll neko[] = {1ll, 10ll, 100ll, 1000ll, 10000ll, 100000ll, 1000000ll, 10000000ll, 100000000ll, 1000000000ll, 10000000000ll, 100000000000ll, 1000000000000ll, 10000000000000ll, 100000000000000ll, 1000000000000000ll};
// ubign<d>: 10^d-based unsigned big integer
template<int dg> class ubign{
    static_assert(1<=dg && dg<=5, "Usage: \"ubign<[dg]> var;\", where 1 <= dg <= 5");
private:
    vector<ll> a;
    void resize(const size_t &n){
        a.resize(n);
    }
    ll &operator [](const int &i){
        return a[i];
    }
    const ll &operator [](const int &i) const{
        return a[i];
    }
    // remove leading zeros
    void trunc(){
        int realsize = size();
        for(; realsize>0 && a[realsize-1]==0; realsize--);
        a.resize(realsize);
    }
    void carry(){
        if(a.empty()){
            return;
        }
        for(int i=0; i<(int)size()-1; i++){
            if(a[i] >= neko[dg]){
                a[i+1] += a[i]/neko[dg];
                a[i] %= neko[dg];
            }
        }
        while(a.back() >= neko[dg]){
            a.push_back(a.back()/neko[dg]);
            a[size()-2] %= neko[dg];
        }
    }
    void borrow(const int &start = 0){
        if(a.empty()){
            return;
        }
        for(int i=start; i<(int)size()-1; i++){
            if(a[i] < 0){
                a[i] += neko[dg];
                a[i+1]--;
            }
        }
        assert(a.back() >= 0);
        trunc();
    }
    // slow multiplication, taking O(mn)-time
    ubign osoi_kakezan(const ubign &b) const{
        if(!size() || !b.size()){
            return 0;
        }
        ubign result;
        result.resize(size()+b.size()-1);
        for(int i=0; i<(int)size(); i++) for(int j=0; j<(int)b.size(); j++){
            result[i+j] += a[i] * b[j];
        }
        result.carry();
        return result;
    }
    // check if (*this)<<start <= b
    bool kiseki(const ubign &b, const int &start) const{
        if(start+size() < b.size()){
            return true;
        }else if(start+size() > b.size()){
            return false;
        }
        for(int i=(int)size()-1; i>=0; i--){
            if(a[i] < b[start+i]){
                return true;
            }else if(a[i] > b[start+i]){
                return false;
            }
        }
        return true;
    }
    // slow division, taking O(mn)-time
    pair<ubign, ubign> osoi_warizan(const ubign &b) const{
        assert(b.size());
        if(size() < b.size()){
            return make_pair(ubign(0), *this);
        }
        ubign q;
        q.resize(size()-b.size()+1);
        if((int)b.size() == 1){
            ll inu = 0;
            for(int i=(int)size()-1; i>=0; i--){
                inu = (inu%b[0])*neko[dg] + a[i];
                q[i] = inu / b[0];
            }
            q.trunc();
            return make_pair(q, ubign(inu%b[0]));
        }else{
            ubign r = (*this);
            ll inu = b[b.size()-1]*neko[dg] + b[b.size()-2];
            for(int i=(int)q.size()-1; i>=0; i--){
                ll musume = 0;
                for(int j=(int)r.size()-1; j>=i+(int)b.size()-2; j--){
                    musume = neko[dg]*musume + r[j];
                }
                ll ub = min(musume/inu+1, neko[dg]), lb = musume/(inu+1);
                ubign slime;
                // the "fake" binary search: ub-lb is either 1 or 2
                while(ub-lb > 1){
                    ll mid = (ub+lb) / 2;
                    slime = ubign(mid)*b;
                    if(slime.kiseki(r, i)){
                        lb = mid;
                    }else{
                        ub = mid;
                    }
                }
                q[i] = lb;
                if(lb > 0){
                    slime = ubign(lb)*b;
                    for(int j=0; j<(int)slime.size(); j++){
                        r[i+j] -= slime[j];
                    }
                    r.borrow(i);
                }
            }
            q.trunc();
            return make_pair(q, r);
        }
    }
public:
    ubign(const char *s = ""){
        a.clear();
        for(int i=(int)strlen(s)-1; i>=0; i-=dg){
            ll d = 0;
            for(int j=0; i-j>=0&&j<=dg-1; j++){
                assert(isdigit(s[i-j]));
                d += (s[i-j]-48)*neko[j];
            }
            a.push_back(d);
        }
        trunc();
    }
    ubign(const string &s): ubign(s.c_str()){}
    ubign(const ull &n){
        if(n == 0){
            a.clear();
        }else if(n < (ull)neko[dg]){
            a.resize(1);
            a[0] = (ll)n;
        }else{
            a.resize(2);
            a[0] = (ll)(n%(ull)neko[dg]);
            a[1] = (ll)(n/(ull)neko[dg]);
            carry();
        }
    }
    ubign(const ll &n){
        assert(n >= 0);
        if(n == 0){
            a.clear();
        }else{
            a.resize(1);
            a[0] = n;
            carry();
        }
    }
    ubign(const int &n): ubign((ll)n){}
    size_t size() const{
        return a.size();
    }
    int operator ()(const int &i) const{
        if(0<=i && i<(int)size()){
            return (int)a[i];
        }
        return 0;
    }
    bool operator <(const ubign &b) const{
        if(size() < b.size()){
            return true;
        }else if(size() > b.size()){
            return false;
        }else{
            for(int i=(int)size()-1; i>=0; i--){
                if(a[i] < b[i]){
                    return true;
                }else if(a[i] > b[i]){
                    return false;
                }
            }
            return false;
        }
    }
    bool operator ==(const ubign &b) const{
        if(size() != b.size()){
            return false;
        }
        return (memcmp(&a[0], &b[0], size()*sizeof(ll)) == 0);
    }
    bool operator >(const ubign &b) const{
        return (b < (*this));
    }
    bool operator >=(const ubign &b) const{
        return !((*this) < b);
    }
    bool operator !=(const ubign &b) const{
        return !((*this) == b);
    }
    bool operator <=(const ubign &b) const{
        return !((*this) > b);
    }
    // multiply by 10^{n*dg}
    ubign operator <<(const int &n) const{
        if(n <= -(int)size()){
            return 0;
        }
        ubign result;
        result.resize(size()+n);
        if(n < 0){
            memcpy(&result[0], &a[-n], result.size()*sizeof(ll));
        }else{
            memcpy(&result[n], &a[0], size()*sizeof(ll));
        }
        return result;
    }
    // divide by 10^{n*dg}
    ubign operator >>(const int &n) const{
        return (*this) << (-n);
    }
    ubign tail(const int &n) const{
        assert(n >= 0);
        if(n >= (int)size()){
            return (*this);
        }
        ubign result;
        result.resize(n);
        memcpy(&result[0], &a[0], n*sizeof(ll));
        result.trunc();
        return result;
    }
    ubign operator ++(){
        if(!size()){
            a.push_back(1ll);
        }else{
            a[0]++;
            if(a[0] >= neko[dg]){
                carry();
            }
        }
        return (*this);
    }
    ubign operator ++(int){
        ubign result = (*this);
        ++(*this);
        return result;
    }
    ubign operator --(){
        assert(size());
        a[0]--;
        if(a[0] < 0){
            borrow();
        }
        return (*this);
    }
    ubign operator --(int){
        ubign result = (*this);
        --(*this);
        return result;
    }
    ubign operator +(const ubign &b) const{
        ubign result;
        if(size() < b.size()){
            result = b;
            for(int i=0; i<(int)size(); i++){
                result[i] += a[i];
            }
        }else{
            result = *this;
            for(int i=0; i<(int)b.size(); i++){
                result[i] += b[i];
            }
        }
        result.carry();
        return result;
    }
    ubign operator +=(const ubign &b){
        return (*this) = (*this) + b;
    }
    ubign operator -(const ubign &b) const{
        assert(size() >= b.size());
        ubign result = *this;
        for(int i=0; i<(int)b.size(); i++){
            result[i] -= b[i];
        }
        result.borrow();
        return result;
    }
    ubign operator -=(const ubign &b){
        return (*this) = (*this) - b;
    }
    ubign operator *(const ubign &b) const{
        if((int)size()<=16 || (int)b.size()<=16){
            return osoi_kakezan(b);
        }
        // O(n log n)-time multiplication
        ubign result;
        int n = size()+b.size()-1;
        result.resize(n);
        for(; (n&-n)!=n; n+=n&-n);
        vector<complex<double>> x(n), y(n);
        for(int i=0; i<(int)size(); i++){
            x[i] = a[i];
        }
        for(int i=0; i<(int)b.size(); i++){
            y[i] = b[i];
        }
        x = fft(x, 1); y = fft(y, 1);
        for(int i=0; i<n; i++){
            x[i] *= y[i];
        }
        x = fft(x, -1);
        for(int i=0; i<(int)result.size(); i++){
            result[i] = (ll)floor(x[i].real()+.5);
        }
        result.carry();
        return result;
    }
    ubign operator *=(const ubign &b){
        return (*this) = (*this) * b;
    }
    pair<ubign, ubign> division(const ubign &b) const{
        assert(b.size());
        if((*this) < b){
            return make_pair(0, *this);
        }
        // this if-statement is important to defeat python's integer type in performance
        if((int)b.size()<=64 || (int)(size()-b.size())<=64){
            return osoi_warizan(b);
        }
        // O(n (log n)^2)-time division
        ll d = b[b.size()-1] * neko[dg];
        if((int)b.size() >= 2){
            d += b[b.size()-2];
        }
        ubign x[2], kitune = ubign(2) << (size()+10);
        x[0] = ubign(neko[3*dg]/(d+1)) << (size()-b.size()+9);
        // Newton's method: x(i+1) := x(i)*(2-b*x(i)) to make x(i) -> 1/b
        // the for-loop is guaranteed to break within O(log n) iterations
        for(int i=0; ; i++){
            x[(i+1)&1] = (x[i&1]*(kitune - b*x[i&1])) >> (size()+10);
            if(!memcmp(&x[0][5], &x[1][5], (x[0].size()-5)*sizeof(ll))){
                break;
            }
        }
        ubign q = ((*this)*x[0]) >> (size()+10), r = (*this) - b*q;
        if(r >= b){
            q++; r -= b;
        }
        return make_pair(q, r);
    }
    ubign operator /(const ubign &b) const{
        return division(b).first;
    }
    ubign operator /=(const ubign &b){
        return (*this) = (*this) / b;
    }
    ubign operator %(const ubign &b) const{
        return division(b).second;
    }
    ubign operator %=(const ubign &b){
        return (*this) = (*this) % b;
    }
    friend istream &operator >>(istream &in, ubign &b){
        string s;
        in >> s;
        for(int i=0; i<(int)s.size(); i++){
            if(!isdigit(s[i])){
                for(int j=(int)s.size()-1; j>=i; j--){
                    in.putback(s[j]);
                }
                s.resize(i);
                break;
            }
        }
        b = s;
        return in;
    }
    friend ostream &operator <<(ostream &out, const ubign &b){
        if(!b.size()){
            return out << '0';
        }else{
            out << b(b.size()-1);
            for(int i=(int)b.size()-2; i>=0; i--){
                out << setw(dg) << setfill('0') << b(i);
            }
            return out;
        }
    }
};

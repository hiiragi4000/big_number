#include<cstring>
#include<cmath>
#include<cassert>
#include<complex>
#include<vector>
#include<iostream>
#include<iomanip>
#include<type_traits>
using namespace std;

#define cd complex<double>
#define ll long long
#define llu unsigned long long
#ifndef M_PI
const double M_PI = acos(-1);
#endif
vector<cd> fft(const vector<cd> &x, const int &inv){
    static int fft_len = 0;
    static vector<cd> loli;
    int n = x.size();
    assert((n&-n)==n && abs(inv)==1);
    if(fft_len < n){
        loli.resize(fft_len=n);
        for(int k=0; k<fft_len; k++){
            loli[k] = exp(cd(0, 2*M_PI*k/fft_len));
        }
    }
    vector<cd> X = x;
    for(int i=1, j=0; i<n; i++){
        for(int k=n>>1; !((j^=k)&k); k>>=1);
        if(i < j){
            swap(X[i], X[j]);
        }
    }
    for(int i=2; i<=n; i*=2){
        int d = (inv==1)? fft_len-(fft_len/i): fft_len/i;
        for(int j=0; j<n; j+=i){
            for(int k=0, a=0; k<i/2; k++, a=(a+d)%fft_len){
                cd s=X[j+k], t=loli[a]*X[j+k+i/2];
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

#define NTT_LEN (1<<27)
static const ll nttp = (15<<27)+1;
vector<ll> ntt(const vector<ll> &x, const int &inv){
    static const ll pr = 31;
    static int ntt_len = 0;
    static vector<ll> loli;
    int n = x.size();
    assert((n&-n)==n && n<=NTT_LEN && abs(inv)==1);
    for(int i=0; i<=n-1; i++) assert(0<=x[i] && x[i]<=nttp-1);
    if(ntt_len < n){
        loli.resize(ntt_len=n);
        loli[0] = 1;
        if(ntt_len >= 2){
            loli[1] = 1;
            for(int i=1; i<=15; i++){
                loli[1] = pr*loli[1]%nttp;
            }
            for(int i=(1<<27)/ntt_len; i>1; i>>=1){
                loli[1] = loli[1]*loli[1]%nttp;
            }
            for(int i=2; i<ntt_len; i++){
                loli[i] = loli[1]*loli[i-1]%nttp;
            }
        }
    }
    vector<ll> X = x;
    for(int i=1, j=0; i<n; i++){
        for(int k=n>>1; !((j^=k)&k); k>>=1);
        if(i < j) swap(X[i], X[j]);
    }
    for(int i=2; i<=n; i*=2){
        int d = (inv==1)? ntt_len-(ntt_len/i): ntt_len/i;
        for(int j=0; j<n; j+=i){
            for(int k=0, a=0; k<i/2; k++, a=(a+d)%ntt_len){
                ll s = X[j+k], t = loli[a]*X[j+k+i/2]%nttp;
                X[j+k] = (s+t)%nttp;
                X[j+k+i/2] = (s-t+nttp)%nttp;
            }
        }
    }
    if(inv == -1){
        for(int i=0; i<n; i++){
            X[i] = X[i]*(nttp-(nttp-1)/n)%nttp;
        }
    }
    return X;
}

static const ll neko[] = {1ll, 10ll, 100ll, 1000ll, 10000ll, 100000ll, 1000000ll, 10000000ll, 100000000ll, 1000000000ll, 10000000000ll, 100000000000ll, 1000000000000ll, 10000000000000ll, 100000000000000ll, 1000000000000000ll};
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
    ubign(const llu &n){
        if(n == 0){
            a.clear();
        }else if(n < (llu)neko[dg]){
            a.resize(1);
            a[0] = (ll)n;
        }else{
            a.resize(2);
            a[0] = (ll)(n%(llu)neko[dg]);
            a[1] = (ll)(n/(llu)neko[dg]);
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
    ubign operator <<=(const int &n){
        return (*this) = (*this) << n;
    }
    ubign operator >>(const int &n) const{
        return (*this) << (-n);
    }
    ubign operator >>=(const int &n){
        return (*this) = (*this) >> n;
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
        ubign result;
        int n = size()+b.size()-1;
        result.resize(n);
        for(; (n&-n)!=n; n+=n&-n);
        vector<cd> x(n), y(n);
        for(int i=0; i<(int)size(); i++) x[i] = a[i];
        for(int i=0; i<(int)b.size(); i++) y[i] = b[i];
        x = fft(x, 1); y = fft(y, 1);
        for(int i=0; i<n; i++) x[i] *= y[i];
        x = fft(x, -1);
        if(n*neko[2*dg] < 1e14){
            for(int i=0; i<(int)result.size(); i++){
                result[i] = (ll)floor(x[i].real()+.5);
            }
        }else{
            vector<ll> xi(n), eta(n);
            for(int i=0; i<(int)size(); i++) xi[i] = a[i];
            for(int i=0; i<(int)b.size(); i++) eta[i] = b[i];
            xi = ntt(xi, 1); eta = ntt(eta, 1);
            for(int i=0; i<n; i++) xi[i] = xi[i]*eta[i]%nttp;
            xi = ntt(xi, -1);
            for(int i=0; i<(int)result.size(); i++){
                ll q = floor((x[i].real()-xi[i])/nttp+.5);
                result[i] = q*nttp+xi[i];
            }
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
        if((int)b.size()<=64 || (int)(size()-b.size())<=64){
            return osoi_warizan(b);
        }
        ll b0 = b[b.size()-1] * neko[dg];
        if((int)b.size() >= 2){
            b0 += b[b.size()-2];
        }
        ubign x = ubign(neko[3*dg]/(b0+1));
        int k = 1;
        for(; ; k++){
            int d = (1<<(k-1))+2;
            ubign eta = b>>((int)b.size()-d);
            if((int)b.size() > d){
                eta++;
            }
            ubign two=ubign(2)<<(d-1), zeta=((eta*x)>>(d/2+1))+1;
            x = (x*(two-zeta))>>(d/2);
            if(1<<(k-1) >= (int)(size()-b.size()+1)){
                break;
            }
        }
        ubign q=((*this)*x)>>((1<<(k-1))+1+b.size()), r=(*this)-b*q;
        if(r >= b){
            q++, r-=b;
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
#undef cd
#undef ll
#undef llu

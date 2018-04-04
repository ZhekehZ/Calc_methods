#include <bits/stdc++.h>

using namespace std;

struct Matrix{
	// Аккуратнее с этим говном, реализовано \
	меньше половины ожидаемых методов, ибо мне лень
	int n, m;
	double * data;

	void clear(){
		fill_n(data, n*m, 0);
	}

	void ident(){
		clear();
		for(int i = 0; i < n; i++)
			(*this)[i][i] = 1;
	}

	Matrix(int n, int m) : n(n), m(m), data(new double[n*m]){
		clear();
	}

	Matrix(const std::string & src){
		std::fstream fin(src);
		fin >> n >> m;
		data = new double[n * m]; 		
		int count = 0;
		while(count < n * m){
			fin >> data[count];
			count++;
		}	
	}

	Matrix(const Matrix & mat): n(mat.n), m(mat.m){
		data = new double[n*m];
		copy(mat.data, mat.data + (n*m), data);
	}

	Matrix& operator=(const Matrix & mat){
		n = mat.n;
		m = mat.m;
		data = new double[n*m];
		copy(mat.data, mat.data + (n*m), data);
		return (*this);
	}

	Matrix join_r(const Matrix & mat) const{
		Matrix n_mat(n, m + mat.m);
		for(int i = 0; i < mat.n; i++){
			for(int k = 0; k < m; k++){
				n_mat[i][k] = (*this)[i][k];
			}
			for(int k = 0; k < mat.m; k++){
				n_mat[i][k + m] = mat[i][k];
			}
		}
		return n_mat;
	}

	void print(std::ostream & out = std::cout) const{
		out.precision(10);
		for(int i = 0; i < n; i++){
			out << '\t';
			for(int k = 0; k < m; k++)
				out << setw(15) << data[i*m + k] << ' ';
			out << '\n';
		}
		out << '\n';
	}

	double* operator[](int i) const{
		return data + i * m;
	}

	Matrix operator-(const Matrix & mat) const{
		Matrix ret(*this);
		for(int i = 0; i < n; i++)
			for(int k = 0; k < m; k++)
				ret[i][k] -= mat[i][k];
		return ret;
	}

	Matrix operator+(const Matrix & mat) const{
		Matrix ret(*this);
		for(int i = 0; i < n; i++)
			for(int k = 0; k < m; k++)
				ret[i][k] += mat[i][k];
		return ret;
	}

	Matrix operator*(const Matrix & mat) const{
		Matrix n_mat(n, mat.m);
		for(int i = 0; i < n; i++){
			for(int k = 0; k < mat.m; k++){
				for(int j = 0; j < m; j++){
					n_mat[i][k] += (*this)[i][j]*mat[j][k];
				}
			}
		}
		return n_mat;
	}

	Matrix& T(){
		double * n_data = new double[n*m];
		for(int i = 0; i < m; i++)
			for(int k = 0; k < n; k++)
				n_data[i * n + k] = data[k * m + i];
		std::swap(data, n_data);
		delete [] n_data;
		return *this;
	}

	double N1() const{
		double res = 0;
		for(int k = 0; k < m; k++){
			double temp = 0;
			for(int i = 0; i < n; i++)
				temp += abs((*this)[i][k]);
			if(temp > res)
				res = temp;
		}
		return res;
	}

	double Ninf() const{
		double res = 0;
		for(int k = 0; k < m; k++){
			double temp = 0;
			for(int i = 0; i < n; i++)
				temp += abs((*this)[k][i]);
			if(temp > res)
				res = temp;
		}
		return res;
	}

	double N2_vector_only(){
		double sum = 0;
		for(int i = 0; i < n; i++)
			sum += (*this)[i][0] * (*this)[i][0];
		return sqrt(sum);
	}

	~Matrix(){
		delete [] data;
	}
	
	static void first_step(Matrix &A){
	for(int i = 0; i < A.n; i++){
			for(int k = A.m - 1; k > -1; k--){
				A[i][k] /= A[i][i];
			}
			for(int k = i+1; k < A.n; k++){
				for(int j = i + 1; j < A.m; j++){
					A[k][j] -= A[k][i] * A[i][j];
				}
				A[k][i] = 0;
			}
		}
	}

	static Matrix second_step(Matrix &A){
		Matrix mat(A.n, A.m - A.n);
		for(int i = 0; i < A.m - A.n; i++){
			for(int k = A.n - 1; k > -1; k--){
				mat[k][i] = A[k][A.n + i];
				for(int j = k + 1; j < A.n; j++){
					mat[k][i] -= A[k][j] * mat[j][i];
				}
			}
		}
		return mat;
	}

	Matrix inv(){
		Matrix E(n,m);
		E.ident();
		Matrix A1(this->join_r(E));
		first_step(A1);
		return second_step(A1);
	}

	double cond(){
		return this->inv().N1() * this->N1();
	}

	Matrix solve_eq(const Matrix& b) const{
		Matrix forGauss(this->join_r(b));
		first_step(forGauss);
		return second_step(forGauss);
	}

	void getLU(Matrix & L, Matrix & U){
		Matrix & A = (*this);
		for(int i = 0 ; i < n; ++i){
			for(int j = i; j < n; ++j){
				double sum = 0;
				for(int k = 0; k < i; k++){
					sum += L[j][k]*U[k][i];
				}
				L[j][i] = A[j][i] - sum;
			
				sum = 0;
				for(int k = 0; k < i; k++){
					sum += L[i][k]*U[k][j];
				}
				U[i][j] = (A[i][j] - sum) / L[i][i];
			}
		}
	}

	Matrix ultra_gauss(const Matrix & b) const{

		Matrix A1(*this);
		vector<int> pos(A1.n, 0);
		for(int i = 0; i < n; i++)
			pos[i] = i;
		for(int q = 0; q < m; q++){
			for(int k = 0; k < m; k++){
				bool ok = true;
				for(int j = k; j < n; j++){
					ok &= abs(A1[k][q]) >= abs(A1[k][j]);
				}
				if(ok){
					for(int i = 0; i < m; i++){
						swap(A1[i][q], A1[i][k]);
					}
					swap(pos[q], pos[k]);
				}
			}
		}

		Matrix x = A1.solve_eq(b);
		Matrix x1(x.n, x.m);

		for(int i = 0; i < pos.size(); i++){
			x1[pos[i]][0] = x[i][0];
		}
		return x1;
	}

	void normalize_vector_only(){
		double norm = this->N2_vector_only();
		if(norm < 1e-9)
			return;
		for(int i = 0; i < n; i++)
			(*this)[i][0] /= norm;
	}

	double Max(){
		double mx = (*this)[0][0];
		for(int i = 0; i < n; i++)
		for(int j = 0; j < m; j++)
			mx = max(mx, (*this)[i][j]);
		return mx;
	}
};

Matrix operator*(double d, const Matrix & m){
	Matrix nm(m);
	for(int i = 0; i < nm.n; ++i)
		for(int j = 0; j < nm.m; ++j)
			nm[i][j] *= d;
	return nm;
}
ostream& operator<<(ostream& os, Matrix m){
	stringstream ss;
	m.print(ss);
	os << ss.str();
	return os;
}


double delta(const Matrix& x1, const Matrix& x2){
	return (x1 - x2).N1() / x1.N1();
}

Matrix R(Matrix A, Matrix x, Matrix b){
	return b - A*x; 
}

void Transform_D(Matrix & A, Matrix & b){
	for(int i = 0; i < b.n; i++)
		b[i][0] /= A[i][i];
	for(int i = 0; i < A.n; i++){
		double tmp = A[i][i];
		for(int j = 0; j < A.n; j++){
			A[i][j] /= -tmp;
		}
		A[i][i] = 0;
	}
}

double aprior(const Matrix & H, const Matrix & g, int k){
	double t = H.Ninf();
	return pow(t, k)/(1 - t)*g.Ninf();
}

double aposter(const Matrix & H, const Matrix x_x1){
	return aprior(H, x_x1, 1);
}

Matrix s_iter(const Matrix & H, const Matrix & g, 
			const Matrix & x0, int count){
	Matrix x(x0);
	for(int i = 0; i < count; ++i){
		Matrix xk(x.n, x.m);
		for(int j = 0; j < x.n; ++j){
			for(int k = 0; k < H.m; ++k){
				xk[j][0] += H[j][k] * x[k][0];
			}
			xk[j][0] += g[j][0];
		}
		swap(x, xk);
	}
	return x;
}

double getSpectrRad(const Matrix & H, const Matrix & g, 
			const Matrix & x0, int count){
    Matrix x(x0);
	double d1, d2;
	for(int i = 0; i < count; ++i){
		Matrix xk(x.n, x.m);
		for(int j = 0; j < x.n; ++j){
			for(int k = 0; k < H.m; ++k){
				xk[j][0] += H[j][k] * x[k][0];
			}
			xk[j][0] += g[j][0];
		}
		if(i == count - 1)
			d1 = (x - xk).Ninf();
		if(i == count - 2)
			d2 = (x - xk).Ninf();
		swap(x, xk);
	}
	return d1 / d2;
}

Matrix Lusterik(const Matrix & x1, const Matrix & x0, 
			double lambda){
	return	x0 + 1 / (1 - lambda) * (x1 - x0);	
}

Matrix relax_iter(const Matrix & H, const Matrix & g,
			const Matrix & x0, int count, double q = 1){
	Matrix x(x0);
	for(int k = 0; k < count; k++){
		Matrix xk(x.n, x.m);
		for(int i = 0; i < x.n; i++){
			for(int j = 0; j < i - 1; j++)
				xk[i][0] += xk[j][0] * H[i][j];
			for(int j = i - 1; j < x.n; j++)
				xk[i][0] += x[j][0] * H[i][j];
			xk[i][0] += g[i][0];
			xk[i][0] *= q;
			xk[i][0] += x[i][0] * (1 - q);	
		}
		swap(x, xk);
	}
	return x;
}

Matrix seid_iter(const Matrix & H, const Matrix & g, 
			const Matrix & x0, int count){
	return relax_iter(H, g, x0, count);
}

Matrix relax_opt(const Matrix & H, const Matrix & g,
			const Matrix & x0, int count, double sp){
	double q = 2 / (1 + sqrt(1 - pow(sp, 2)));
	return relax_iter(H, g, x0, count, q);
}

pair<double, Matrix> Step(const Matrix & A, double eps, int kmax){
	Matrix Y(A.n, 1);
	for(int i = 0; i < Y.n; i++)
		Y[i][0] = rand()%10/50.0 - 0.5; 

	Matrix Y1(Y.n, 1), l(Y.n, 1);

	for(int k = 0; k < kmax; k++){
		Y1 = A*Y;
		Matrix l1 = Y1;/*
		for(int i = 0; i < A.n; i++)
			l1[i][0] /= Y[i][0];
*/
		for(int i = 0; i < A.n; ++i)
			l1[i][0] = Y1[i][0] / Y[i][0];

		double mx = Y1.N1();

		for(int i = 0; i < A.n; ++i)
			Y1[i][0] /= mx;

		if((l1- l).N1() < eps){
			Y1.normalize_vector_only();
			return {l1.Max(), Y1};
		}
		swap(Y, Y1);
		swap(l, l1);
	}
	Y1.normalize_vector_only();
	return {l.Max(), Y1};
}

pair<double, Matrix> Vilandt(const Matrix & A, double l, double eps, int kmax){
	Matrix E = A; E.ident();

	Matrix Y(A.n, 1);
	for(int i = 0; i < Y.n; i++)
		Y[i][0] = rand()%10/50.0; 

	Matrix Y1(Y.n, 1);

	for(int k = 0; k < kmax; k++){
		Matrix W = (A - l * E);
		auto tmp = Step(W.inv(), eps, kmax);
		double mu = tmp.first;
		Y1 = tmp.second;
		l += 1 / mu;
		if(abs(1/mu) < eps)
			break;
		swap(Y, Y1);
	}
	return {l, Y};
}

inline double sqr(double x){
	return x*x;
}

inline double sign(double x){
	return (x < 0) ? -1 : 1;
}

pair<vector<double>, Matrix> rotaions(Matrix & A, double eps, int kmax){
	Matrix X = A; X.ident();

	int count;

	for(count = 0; count < kmax; ++count){
		double umax = 0;
		int jk = -1, ik = -1;
		for(int i = 0; i < A.n; ++i){
			for(int j = 0; j < i; ++j){
				if(jk == -1 || abs(A[i][j]) > umax){
					umax = abs(A[i][j]);
					ik = i;
					jk = j;
				}
			}
		} 
		
		if(umax < eps)
			break;

		double t = A[ik][ik] - A[jk][jk];
		double q = sign(A[ik][jk] * t);
		double d = sqrt(sqr(t) + 4 * sqr(A[ik][jk]));
		double c = sqrt(0.5 * (1 + abs(t) / d));
		double s = sqrt(0.5 * (1 - abs(t) / d)) * q;

		double aikik = A[ik][ik], ajkjk = A[jk][jk], aikjk = A[ik][jk];
		
		for(int i = 0; i < A.n; ++i){
			if(i != ik && i != jk){
				double t = A[i][ik];
				A[i][ik] = A[ik][i] = c * A[i][ik] + s * A[i][jk];
				A[i][jk] = A[jk][i] = -s * t + c * A[i][jk];
			}
		}
		A[ik][ik] = c * c * aikik + 2 * c * s * aikjk + s * s * ajkjk;
		A[jk][jk] = s * s * aikik - 2 * c * s * aikjk + c * c * ajkjk;
		A[ik][jk] = A[jk][ik] = (c * c - s * s) * aikjk + c * s * (ajkjk - aikik); // это ноль

		for(int i = 0; i < A.n; ++i){
			double t = X[i][ik];
			X[i][ik] = c * X[i][ik] + s * X[i][jk];
			X[i][jk] = -s * t + c * X[i][jk];
		}
	}

	vector<double> res(X.n);
	for(int i = 0; i < A.n; ++i){
		res[i] = A[i][i];
	}
	cout << "A_k = \n" <<  A << '\n' << "Iters: " << count << '\n';
	return {res, X};
}

double Fredgolm_eq(double (*u)(double), double (*H)(double, double), 
													double a, double b){
														
}

int main(){
	cout.precision(10);
#if 0// ex 1
	Matrix A("A");
	Matrix b("b");

	cout << "A =\n";	A.print();
	cout << "b =\n";	b.print();

	auto x = A.solve_eq(b);
	cout << "x* =\n";	x.print();

	Matrix H(A); 
	Matrix g(b);
	Transform_D(H, g);
	cout << "H = \n";	H.print();
	cout << "g = \n";	g.print();
	cout << "|H| = " << H.Ninf() << "\n\n";
	
	double spectr = getSpectrRad(H, g, Matrix(g.n, g.m), 20);
	
	Matrix x6 = s_iter(H, g, Matrix(g.n, g.m), 6);
	Matrix x7 = s_iter(H, g, Matrix(g.n, g.m), 7);
	cout << "x7 = \n"; x7.print();
	cout << "aprior:\t|x7-x*| <= " << aprior(H, g, 7) << "\n\n";
	cout << "fact:\t|x7-x*| = " << (x - x7).Ninf() << "\n\n";
	cout << "aposter:|x7-x*| <= " << aposter(H, x7-x6) << "\n\n";
	Matrix x7_ = Lusterik(x7, x6, spectr);
	cout << "Lust: x7^ = \n"; x7_.print();
	cout << "Lust fact: |x7^-x*| = " << (x7_ - x).Ninf() << "\n\n";

	Matrix sx7 = seid_iter(H, g, Matrix(g.n, g.m), 7);
	cout << "sx7 = \n"; sx7.print();
	cout << "fact:\t|sx7-x*| = " << (sx7 - x).Ninf() << "\n\n";

	Matrix relx7 = relax_opt(H, g, Matrix(g.n, g.m), 7, spectr);
	cout << "relx7 = \n"; relx7.print();
	cout << "fact:\t|relx7-x*| = " << (relx7 - x).Ninf() << "\n\n";
	cout << "spectr = " << spectr << '\n';
#elif 0//ex 2.1
	double lambda_WOLFRAM = -1.40778;

	double eps = 0.0001;
	Matrix A("A_");/*
	cout << "A = \n" << A;
	auto tmp = Step(A, eps, 100);
	cout << "lambda_a = " << tmp.first << '\n';
	cout << "x = \n" << tmp.second;
	cout << "A * x - lambda_a * x= \n" << A * tmp.second - tmp.first * tmp.second;
	Matrix E(A.n, A.m);
	E.ident();
	Matrix B = A - tmp.first * E;
	auto tmp1 = Step(B, eps, 100);
	tmp1.first += tmp.first;
	cout << "lambda_b = " << tmp1.first << '\n';
	cout << "x = \n" << tmp1.second;
	cout << "A * x - lambda_b * x = \n" << A * tmp1.second - tmp1.first * tmp1.second;
	double lambda_min = min(tmp1.first, tmp.first);
	auto x = (lambda_min == tmp1.first) ? tmp1.second : tmp.second;
	cout << "lambda_min = " << lambda_min << '\n';
	cout << "dl = " << lambda_min - lambda_WOLFRAM << '\n';
*/
	cout << "A = \n" << A;
	#if 0//ex 2.2a
	cout << "VILANDT:\n";
	auto tt = Vilandt(A, -2, 0.0001, 100);
	cout << "iters: " << C << '\n';
	cout << "lambda: " << tt.first << "\nx = " << tt.second;
	cout << "R = \n" << R(A, tt.second, tt.first * tt.second);

	cout << "\n\nSTEP:\n";
	auto tmp = Step(A, 0.0001, 100);
	cout << "iters: " << C << '\n';
	cout << "lambda = " << tmp.first << '\n';
	cout << "x = \n" << tmp.second;
	cout << "R = \n" << R(A, tmp.second, tmp.first * tmp.second);
	#else//ex 2.2b
	auto ttt = rotaions(A, eps, 100);
	cout << "x = \n" << ttt.second;
	cout << "l = ";
	Matrix x = ttt.second;
	for(auto a : ttt.first)
		cout << a << "; ";
	cout << '\n';
	/*
	Matrix x1(3,1), x2(3,1), x3(3,1);
	x1[0][0] = x[0][0]; x2[0][0] = x[0][1]; x3[0][0] = x[0][2];
	x1[1][0] = x[1][0]; x2[1][0] = x[1][1]; x3[1][0] = x[1][2];
	x1[2][0] = x[2][0]; x2[2][0] = x[2][1]; x3[2][0] = x[2][2];
	cout << x3 << ttt.first[2];
	cout << R(A, x3, ttt.first[2] * x3);*/
	#endif
#else // ex3

#endif
	return 0;
}
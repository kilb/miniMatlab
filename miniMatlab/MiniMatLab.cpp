// 词法分析.cpp : 定义控制台应用程序的入口点。
//

#include "stdafx.h"
#include "math.h"
#include <iostream>
#include <boost/regex.h>
#include <boost/spirit.hpp>
#include <boost/spirit/home/classic/actor/assign_actor.hpp>
#include <boost/variant.hpp>
#include <boost/noncopyable.hpp>
#include <boost/assign.hpp>
#include <string.h>
#include <boost/variant/apply_visitor.hpp>
#include <boost/variant/recursive_variant.hpp>
#include <Dense>
#include "MiniMatLab.h"

using namespace std;
using namespace boost::spirit;
using namespace Eigen;

string input ;
double x_g,a_g,b_g,eps_g;
int n_g;
int c = 0;
MatBuff m_g;
MatrixXd mat_1, mat_2;
bool mat_valid = TRUE;
VectorXd vec_g;

MatBuff::MatBuff()
{
	col = 0;
	row = 0;
	i = 0;
	count = 0;
	valid = TRUE;
}
bool MatBuff::isValid()
{
	return valid;
}
void MatBuff::inCount()
{
	++count;
}
void MatBuff::ClearCount()
{
	count = 0;
}
void MatBuff::inRow()
{
	++row;
}
void MatBuff::updateCol()
{
	if (col != 0 && col != count)
	{
		valid = FALSE;
	}
	else
	{
		col = count;
		count = 0;
	}
	++row;
}
int MatBuff::Col()
{
	return col;
}
int MatBuff::Row()
{
	return row;
}
int MatBuff::Count()
{
	return count;
}
double MatBuff::Read(int i,int j)
{
	return val[i*col+j];
}

void MatBuff::Push(double num)
{
	if (i < MaxSize)
		val[i++] = num;
}
void MatBuff::Clear()
{
	col = 0;
	row = 0;
	i = 0;
	count = 0;
	valid = TRUE;
}
namespace
{
	stack<double> calc_stack;

	struct do_add
	{
		double operator () (double lhs, double rhs) const
		{
			return lhs + rhs;
		}
	};

	struct do_substract
	{
		double operator () (double lhs, double rhs) const
		{
			return lhs - rhs;
		}
	};

	struct do_multiply
	{
		double operator () (double lhs, double rhs) const
		{
			return lhs * rhs;
		}
	};

	struct do_divide
	{
		double operator () (double lhs, double rhs) const
		{
			return lhs / rhs;
		}
	};
	struct do_cos
	{
		double operator () (double lhs) const
		{
			return cos(lhs);
		}
	};
	struct do_sin
	{
		double operator () (double lhs) const
		{
			return sin(lhs);
		}
	};
	struct do_tan
	{
		double operator () (double lhs) const
		{
			return tan(lhs);
		}
	};
	struct do_acos
	{
		double operator () (double lhs) const
		{
			return acos(lhs);
		}
	};
	struct do_asin
	{
		double operator () (double lhs) const
		{
			return asin(lhs);
		}
	};
	struct do_atan
	{
		double operator () (double lhs) const
		{
			return atan(lhs);
		}
	};
	struct do_log
	{
		double operator () (double lhs) const
		{
			return log(lhs);
		}
	};
	struct do_sqrt
	{
		double operator () (double lhs) const
		{
			return log(lhs);
		}
	};
	

	template <typename op>
	struct do_calc
	{
		void operator () (const char *, const char *) const
		{
			double result = calc_stack.top();
			calc_stack.pop();
			result = op()(calc_stack.top(), result);
			calc_stack.pop();
			calc_stack.push(result);
		}
	};
	template <typename fun>
	struct do_func
	{
		void operator () (const char *, const char *) const
		{
			double result = fun()(calc_stack.top());
			calc_stack.pop();
			calc_stack.push(result);
		}
	};
	void push_real(double d)
	{
		calc_stack.push(d);
	}
	void do_pow(double d)
	{
		double result = pow(calc_stack.top(), d);
		calc_stack.pop();
		calc_stack.push(result);
	}
	
	void push_x(char c)
	{
		calc_stack.push(x_g);
	}
	void do_neg(char const*, char const*)
	{
		//cout << "NEGATE ";
		double result = calc_stack.top();
		calc_stack.pop();
		calc_stack.push(-result);
	}

	double show_result()
	{
		return calc_stack.top();
	}
}

void GetVal(double val)
{
	m_g.Push(val);
	m_g.inCount();
}
void NewRow(char c)
{
	m_g.updateCol();
}

MatrixXd save_mat()
{	
	int row = m_g.Row();
	int col = m_g.Col();
	MatrixXd m(row, col);
	for (int i = 0; i < m_g.Row(); ++i)
		for (int j = 0; j < m_g.Col(); ++j)
			m(i,j) = m_g.Read(i,j);
		return m;
}
void save_mat1(const char* f, const char *l)
{
	m_g.updateCol();
	if (!m_g.isValid())
	{
		mat_valid = FALSE;
		return;
	}
	mat_1 = save_mat();
	m_g.Clear();
}
void save_mat2(const char*f,const char *l)
{
	m_g.updateCol();
	if (!m_g.isValid())
	{
		mat_valid = FALSE;
		return;
	}
	mat_2 = save_mat();
	m_g.Clear();
}
void save_vec(const char* f, const char *l)
{
	VectorXd vec(m_g.Count());
	for (int i = 0; i < m_g.Count(); ++i)
		vec(i) = m_g.Read(0, i);
	vec_g = vec;
	m_g.Clear();
}

struct CalcGrammar : public grammar<CalcGrammar>
{
	template <typename ScannerT>
	struct definition
	{
		rule<ScannerT> const& start() const { return top; }

		explicit definition(const CalcGrammar& self)
		{
			top = exp ;

			exp = term >>
				*((*(blank_p) >> '+' >> *(blank_p)
				>> term[do_calc<do_add>()]) |
				(*(blank_p) >> '-' >> *(blank_p)
				>> term[do_calc<do_substract>()]));
			term = pow_p >>
				*((*(blank_p) >> '*' >> *(blank_p)
				>> pow_p[do_calc<do_multiply>()]) |
				(*(blank_p) >> '/' >> *(blank_p)
				>> pow_p[do_calc<do_divide>()]));
			pow_p = factor >> *(*(blank_p) >> ch_p('^') >> *(blank_p) >> real_p[&do_pow]);
			factor = longest_d[('(' >> *(blank_p) >> exp >> *(blank_p) >> ')')
				| func
				| (*(blank_p) >> '-' >> *(blank_p) >> factor[&do_neg])
				| (*(blank_p) >> '+' >> *(blank_p) >> factor)]
				| real_p[&push_real];
			func = cos_p[do_func<do_cos>()]
				| sin_p[do_func<do_sin>()]
				| log_p[do_func<do_log>()]
				| sqrt_p[do_func<do_sqrt>()]
				| tan_p[do_func<do_tan>()]
				| acos_p[do_func<do_acos>()]
				| asin_p[do_func<do_asin>()]
				| atan_p[do_func<do_atan>()];
			cos_p = str_p("cos") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			sin_p = str_p("sin") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			log_p = str_p("log") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			sqrt_p = str_p("sqrt") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			tan_p = str_p("tan") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			acos_p = str_p("acos") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			asin_p = str_p("asin") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			atan_p = str_p("atan") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
		}
		rule<ScannerT> exp, term, factor, top, func, number, cos_p, sin_p, log_p, sqrt_p, pow_p, var, tan_p, acos_p, asin_p, atan_p;
	};
};

struct FuncGrammar : public grammar<FuncGrammar>
{
	template <typename ScannerT>
	struct definition
	{
		rule<ScannerT> const& start() const { return top; }

		explicit definition(const FuncGrammar& self)
		{
			top = exp ;

			exp = term >>
				*((*(blank_p) >> '+' >> *(blank_p)
				>> term[do_calc<do_add>()]) |
				(*(blank_p) >> '-' >> *(blank_p)
				>> term[do_calc<do_substract>()]));
			term = pow_p >>
				*((*(blank_p) >> '*' >> *(blank_p)
				>> pow_p[do_calc<do_multiply>()]) |
				(*(blank_p) >> '/' >> *(blank_p)
				>> pow_p[do_calc<do_divide>()]));
			pow_p = factor >> *(*(blank_p) >> ch_p('^') >> *(blank_p) >> real_p[&do_pow]);
			factor = longest_d[('(' >> *(blank_p) >> exp >> *(blank_p) >> ')')
				| var
				| func
				| (*(blank_p) >> '-' >> *(blank_p) >> factor[&do_neg])
				| (*(blank_p) >> '+' >> *(blank_p) >> factor)]
				| real_p[&push_real];
			var = ch_p('x')[&push_x];
			func = cos_p[do_func<do_cos>()] 
				  | sin_p[do_func<do_sin>()] 
				  | log_p[do_func<do_log>()] 
				  | sqrt_p[do_func<do_sqrt>()]
				  | tan_p[do_func<do_tan>()]
				  | acos_p[do_func<do_acos>()]
				  | asin_p[do_func<do_asin>()]
				  | atan_p[do_func<do_atan>()];
			cos_p = str_p("cos") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			sin_p = str_p("sin") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			log_p = str_p("log") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			sqrt_p = str_p("sqrt") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			tan_p = str_p("tan") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			acos_p = str_p("acos") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			asin_p = str_p("asin") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
			atan_p = str_p("atan") >> *(blank_p) >> '(' >> *(blank_p) >> exp >> *(blank_p) >> ')';
		}
		rule<ScannerT> exp, term, factor, top, func, number,cos_p,sin_p,log_p,sqrt_p,pow_p,var,tan_p,acos_p,asin_p,atan_p;
	};
};
FuncGrammar func_p;
CalcGrammar calc_p;
boost::spirit::rule<> mat_p = '[' >> *(blank_p) >> (real_p[&GetVal] >> *(blank_p) >> *(',' >> *(blank_p) >> real_p[&GetVal] >> *(blank_p))) >> *(ch_p(';')[&NewRow] >> *(blank_p) >> real_p[&GetVal] >> *(blank_p) >> *(',' >> *(blank_p) >> real_p[&GetVal] >> *(blank_p))) >> *(blank_p) >> ']';
boost::spirit::rule<> vec_p = '[' >> *(blank_p) >> (real_p[&GetVal] >> *(blank_p) >> *(',' >> *(blank_p) >> real_p[&GetVal] >> *(blank_p))) >> *(blank_p) >> ']';
boost::spirit::rule<> mat_mul = mat_p[&save_mat1] >> *(blank_p) >> '*' >> *(blank_p) >> mat_p[&save_mat2];
boost::spirit::rule<> mat_mul2 = (calc_p >> *(blank_p) >> '*' >> *(blank_p) >> mat_p[&save_mat1]) | (mat_p[&save_mat1] >> *(blank_p) >> '*' >> *(blank_p) >> calc_p);
boost::spirit::rule<> mat_add = mat_p[&save_mat1] >> *(blank_p) >> '+' >> *(blank_p) >> mat_p[&save_mat2];
boost::spirit::rule<> mat_tran = mat_p[&save_mat1] >> *(blank_p) >> '.' >> *(blank_p) >> "transpose" >> *(blank_p) >> '(' >> *(blank_p) >> ')' ;
boost::spirit::rule<> mat_conj = mat_p[&save_mat1] >> *(blank_p) >> '.' >> *(blank_p) >> "conjugate" >> *(blank_p) >> '(' >> *(blank_p) >> ')';
boost::spirit::rule<> mat_adj = mat_p[&save_mat1] >> *(blank_p) >> '.' >> *(blank_p) >> "adjoint" >> *(blank_p) >> '(' >> *(blank_p) >> ')';
boost::spirit::rule<> solve_p = str_p("solve") >> *(blank_p) >> '(' >> *(blank_p) >> func_p >> *(blank_p) >> ',' >> *(blank_p) >> real_p[assign_a(a_g)] >> *(blank_p) >> ',' >> *(blank_p) >> real_p[assign_a(b_g)] >> *(blank_p) >> ',' >> *(blank_p) >> real_p[assign_a(eps_g)] >> *(blank_p) >> ')';
boost::spirit::rule<> sort_p = str_p("sort") >> *(blank_p) >> '(' >> *(blank_p) >> vec_p[&save_vec] >> *(blank_p) >> ')';
boost::spirit::rule<> descend_p = str_p("descend") >> *(blank_p) >> '(' >> *(blank_p) >> vec_p[&save_vec] >> *(blank_p) >> ')';
boost::spirit::rule<> integ_p = str_p("integ") >> *(blank_p) >> '(' >> *(blank_p) >> func_p >> *(blank_p) >> ',' >> *(blank_p) >> real_p[assign_a(a_g)] >> *(blank_p) >> ',' >> *(blank_p) >> real_p[assign_a(b_g)] >> *(blank_p) >> ',' >> *(blank_p) >> int_p[assign_a(n_g)] >> *(blank_p) >> ')';
//boost::spirit::rule<>;

double Cotes()
{
	double sum = 0.0;
	double gaps = (b_g - a_g) / double(n_g);  //每个间隔的长度
	double h = gaps / 2.0;
	double val1, val2, val3, val4, val5;
	for (int i = 0; i < n_g; i++)
	{
		x_g = a_g + i*gaps;
		parse(input.c_str(), integ_p, space_p);
		val1 = 7.0 * show_result();
		x_g = a_g + i*gaps + 0.25*gaps;
		parse(input.c_str(), integ_p, space_p);
		val2 = 32.0 * show_result();
		x_g = a_g + i*gaps + 0.5*gaps;
		parse(input.c_str(), integ_p, space_p);
		val3 = 12.0 * show_result();
		x_g = a_g + i*gaps + 0.75*gaps;
		parse(input.c_str(), integ_p, space_p);
		val4 = 32.0 * show_result();
		x_g = a_g + (i + 1)*gaps;
		parse(input.c_str(), integ_p, space_p);
		val5 = 7.0 * show_result();
		sum += (h / 45.0) * (val1 +
			val2 +
			val3 +
			val4 +
			val5);
	}
	return sum;
}
bool BinSolve(double & x)
{
	double m = 0.0;
	double y1, y2;
	double a = a_g, b = b_g;
	do
	{
		x_g = a;
		parse(input.c_str(), solve_p, space_p);
		y1 = show_result();
		x_g = b;
		parse(input.c_str(), solve_p, space_p);
		y2 = show_result();
		if (y1*y2 > 0)
		{
			return false;
		}
		if (y1*y2 == 0)
		{
			if (y1 == 0)
				x = a;
			else
				x = b;
			return true;
		}
		else
		{
			m = (a + b) / 2.0;
			x_g = m;
			parse(input.c_str(), solve_p, space_p);
			y2 = show_result();
			if (y1*y2 > 0)
			{
				a = m;
			}
			else
			{
				b = m;
			}
		}
	} while (abs(a - b) >= eps_g);
	x = m;
	return true;
}
int do_action()
{
	
	m_g.Clear();
	mat_valid = TRUE;
	if (parse(input.c_str(), mat_mul, space_p).full == 1)
	{
		MatrixXd m;
		if (mat_valid)
		{
			if (mat_1.cols() == mat_2.rows())
			{
				m = mat_1 * mat_2;
				cout << m << endl;
				
			}
			else
			{
				cout << "错误：矩阵的维度不一致！" << endl;
			}
		}
		else
		{
			cout << "错误：输入的矩阵不正确！" << endl;
		}
		return 1;
	}
	else if (parse(input.c_str(), mat_mul2, space_p).full == 1)
	{
		MatrixXd m;
		if (mat_valid)
		{
			m = mat_1 * show_result();
			cout << m << endl;
		}
		else
		{
			cout << "错误：输入的矩阵不正确！" << endl;
		}
		return 1;
	}
	else if (parse(input.c_str(), mat_tran, space_p).full == 1)
	{
		MatrixXd m;
		if (mat_valid)
		{
			m = mat_1.transpose();
			cout << m << endl;
		}
		else
		{
			cout << "错误：输入的矩阵不正确！" << endl;
		}
		return 1;
	}
	else if (parse(input.c_str(), mat_conj, space_p).full == 1)
	{
		MatrixXd m;
		if (mat_valid)
		{
			m = mat_1.conjugate();
			cout << m << endl;
		}
		else
		{
			cout << "错误：输入的矩阵不正确！" << endl;
		}
		return 1;
	}
	else if (parse(input.c_str(), mat_adj, space_p).full == 1)
	{
		MatrixXd m;
		if (mat_valid)
		{
			if (mat_1.cols() == mat_1.rows())
			{
				m = mat_1.adjoint();
				cout << m << endl;

			}
			else
			{
				cout << "错误：矩阵的行列不一致！" << endl;
			}
		}
		else
		{
			cout << "错误：输入的矩阵不正确！" << endl;
		}
		return 1;
	}
	else if (parse(input.c_str(), mat_add, space_p).full == 1)
	{
		MatrixXd m;
		if (mat_valid)
		{
			if (mat_1.cols() == mat_2.cols() && mat_1.rows() == mat_2.rows())
			{
				m = mat_1 + mat_2;
				cout << m << endl;
			}
			else
			{
				cout << "错误：矩阵的维度不一致！" << endl;
			}
		}
		else
		{
			cout << "错误：输入的矩阵不正确！" << endl;
		}
		return 1;
	}
	else if (parse(input.c_str(), descend_p, space_p).full == 1)
	{
		std::sort(vec_g.data(), vec_g.data() + vec_g.size());
		vec_g.reverseInPlace();
		cout << vec_g << endl;
		return 1;
	}
	else if (parse(input.c_str(), calc_p, space_p).full == 1)
	{
		cout << show_result() << endl;
		return 1;
	}
	else if (parse(input.c_str(), sort_p, space_p).full == 1)
	{
		std::sort(vec_g.data(), vec_g.data() + vec_g.size());
		cout << vec_g << endl;
		return 1;
	}
	else if (parse(input.c_str(), solve_p, space_p).full == 1)
	{
		double x;
		if (a_g > b_g)
			return 0;
		if (BinSolve(x))
			cout << x << endl;
		else
			cout << "在给定区间内方程无根" << endl;
		return 1;
	}
	else if (parse(input.c_str(), integ_p, space_p).full == 1)
	{
		if (a_g > b_g)
			return 0;
		cout << Cotes() << endl;
		return 1;
	}
	else
		cout << "语法错误！" << endl;
	return 0;
}
int _tmain(int argc, _TCHAR* argv[])
{
	while (TRUE)
	{
		cout << ">> ";
		getline(cin, input);
		do_action();
	}
}
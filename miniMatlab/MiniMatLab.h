#define MaxSize 160000
class MatBuff
{
	int col;
	int row;
	int count;
	bool valid;
	int i;
	double val[MaxSize];
public:
	MatBuff();
	void Push(double num);
	void Clear();
	double Read(int i, int j);
	void inCount(void);
	void inRow(void);
	void updateCol(void);
	int Row(void);
	int Col(void);
	int Count(void);
	void ClearCount(void);
	bool isValid();
};
void GetVal(double val);
void NewRow(char c);
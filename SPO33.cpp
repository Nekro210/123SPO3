#include "windows.h"
#include <iostream>
#include <iomanip>
#include <vector>
#include <iterator>
#include <fstream>
#include <math.h>
#include <stdexcept>
#include <algorithm>
#include <tchar.h>
#include <tlhelp32.h>
using namespace std;;

CRITICAL_SECTION g_cs = {0};

struct Params
{
    double** f;
    int n;

};

__int64 FileTimeToQuadWord(PFILETIME pft)
{
    return(Int64ShllMod32(pft->dwHighDateTime, 32) | pft->dwLowDateTime);
}

ULONGLONG getWorkTime(FILETIME* from, FILETIME* to, int del = 10)
{
    ULARGE_INTEGER ulF;
    ulF.HighPart = from->dwHighDateTime;
    ulF.LowPart = from->dwLowDateTime;

    ULARGE_INTEGER ulT;
    ulT.HighPart = to->dwHighDateTime;
    ulT.LowPart = to->dwLowDateTime;

    ULARGE_INTEGER def;
    def.QuadPart = (ulT.QuadPart - ulF.QuadPart) / del;
    return def.QuadPart;
}
// создаем матрицу размера n
double** new2DArray(const int n)
{
    double** arr = new double* [n];
    for (int i = 0; i < n; ++i)
        arr[i] = new double[n];
    return arr;
}


// для удаления двумерных массивов
void delete2DArray(double** arr, const int m)
{
    for (int i = 0; i < m; ++i)
        delete[] arr[i];
    delete[] arr;
}

// вывод матрицы
void print2DArray(double** arr, const int n)
{
    for (int i = 0; i < n; ++i)
    {
        for (int j = 0; j < n; ++j)
            cout << std::setw(4) << arr[i][j] << " ";
        cout << '\n';
    }
    cout << '\n';
}

// перемножение матриц размерности n
double** MultiplyWithOutAMP(const int n, double** mtrx, double** tmtrx) {
    double** product = new2DArray(n);
    for (int row = 0; row < n; row++) {
        for (int col = 0; col < n; col++) {
            product[row][col] = 0;
        }
    }
    for (int row = 0; row < n; row++) {
        for (int col = 0; col < n; col++) {
            // Multiply the row of A by the column of B to get the row, column of product.
            for (int inner = 0; inner < n; inner++) {
                product[row][col] += mtrx[row][inner] * tmtrx[inner][col];
            }
            //cout << product[row][col] << "  ";
        }
        //cout << "\n";
    }
    //cout << "\n";
    return product;
}

// инвертирование матрицы
double** inv(double** A, const int N)
{
    double temp;
    double** A2 = A;
    double** E = new double* [N];

    for (int i = 0; i < N; i++)
        E[i] = new double[N];

    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
        {
            E[i][j] = 0.0;

            if (i == j)
                E[i][j] = 1.0;
        }

    for (int k = 0; k < N; k++)
    {
        temp = A2[k][k];

        for (int j = 0; j < N; j++)
        {
            A2[k][j] /= temp;
            E[k][j] /= temp;
        }

        for (int i = k + 1; i < N; i++)
        {
            temp = A2[i][k];

            for (int j = 0; j < N; j++)
            {
                A2[i][j] -= A[k][j] * temp;
                E[i][j] -= E[k][j] * temp;
            }
        }
    }

    for (int k = N - 1; k > 0; k--)
    {
        for (int i = k - 1; i >= 0; i--)
        {
            temp = A2[i][k];

            for (int j = 0; j < N; j++)
            {
                A2[i][j] -= A2[k][j] * temp;
                E[i][j] -= E[k][j] * temp;
            }
        }
    }

    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            A2[i][j] = E[i][j];

    for (int i = 0; i < N; i++)
        delete[] E[i];

    delete[] E;
    //print2DArray(A2, N);
    return A2;
}

// полином для вычисления собственных чисел
double f(vector<double> coefs, double x) {
    int biggest_power = coefs.size();

    double result = 0;
    for (int i = biggest_power - 1; i >= 1; i--) {
        result = result + coefs[i] * pow(x, i);
    }
    result = result + coefs[0];
    return result;
}

// Безу
vector<double> gorner(vector<double> coefs, double root) {
    reverse(coefs.begin(), coefs.end());
    vector<double> new_coefs(coefs.size() - 1);
    new_coefs[0] = coefs[0];
    for (int i = 1; i < new_coefs.size(); i++) {
        new_coefs[i] = coefs[i] + new_coefs[i - 1] * root;
    }

    reverse(new_coefs.begin(), new_coefs.end());
    return new_coefs;
}

// вычисление матрицы b
double** cr_b(double** f, const int n, int o) {
    double** b = new2DArray(n);

    for (int k = 0; k < n; ++k) {
        for (int z = 0; z < n; ++z) {
            if (k == z) {
                b[k][z] = 1;
            }
            else {
                b[k][z] = 0;
            }
        }
    }
    for (int j = 0; j < n; j++) {
        if (j != n - 2 - o) {
            b[n - 2 - o][j] = -f[n - 1 - o][j] / f[n - 1 - o][n - 2 - o];
        }
        else {
            b[n - 2 - o][j] = 1 / f[n - 1 - o][n - 2 - o];
        }

    }
    return b;
}

// метод секущих
double secant(double a, double b, vector<double> coefs) {
    double x1 = a;
    double x2 = b;
    double tmp = 0;
    const double e = 0.0001;

    while (fabs(x2 - x1) > e) {
        tmp = x2;
        x2 = x2 - (x2 - x1) * f(coefs, x2) / (f(coefs, x2) - f(coefs, x1));
        x1 = tmp;
    }

    return x2;
}

// вычисление радиуса
double find_radius(vector<double> coefs) {
    coefs.pop_back();
    reverse(coefs.begin(), coefs.end());
    for (int i = 0; i < coefs.size(); i++) {
        coefs[i] = pow(fabs(coefs[i]), (double)1 / (i + 1));
    }
    sort(coefs.begin(), coefs.end());
    double radius = 0;
    if (coefs.size() >= 2) {
        radius = coefs[coefs.size() - 1] + coefs[coefs.size() - 2];
    }
    else {
        radius = coefs[coefs.size() - 1];
    }
    //cout << "radius=" << radius;
    return radius;
}

// нахождение собственных чисел матрицы из матрицы Фробениуса
vector<double> root_finder(vector<double> coefs) {
    int num_roots = coefs.size() - 1;
    double radius = 0;
    vector<double> roots(num_roots);
    for (int i = 0; i < num_roots; i++) {
        radius = find_radius(coefs);
        roots[i] = secant(-radius, radius, coefs);
        coefs = gorner(coefs, roots[i]);
    }

    return roots;
}

// Данилевский
void DAN(double** f, const int n) {

    setlocale(LC_ALL, "Russian");
    cout << "\nFirst thread: " << GetCurrentThreadId() <<"\n";
    double** b = cr_b(f, n, 0);
    //print2DArray(b, n);
    f = MultiplyWithOutAMP(n, inv(b, n), MultiplyWithOutAMP(n, f, b));
    //print2DArray(f, n);
    int o = 0;
    for (int i = 1; i < n - 1; ++i) {
        b = cr_b(f, n, i);
        //print2DArray(b, n);
        f = MultiplyWithOutAMP(n, inv(b, n), MultiplyWithOutAMP(n, f, b));
        //print2DArray(f, n);
    }
    
    cout << "\nDanilevskiy" << endl << endl;
    cout << "Frobenius (P)" << endl;
    


    cout << "\n";
    vector<double> P(n + 1);
    P[n] = 1;
    int kb = 0;
    for (int j = n - 1; j >= 0; j--) {
        P[j] = -(f[0][kb]);
        kb++;
    }

    for (int j = 0; j < n; ++j)
        cout << f[0][j] << " ";



    delete2DArray(f, n);
    delete2DArray(b, n);


    //cout << '\n' << P[j] << "\n";

    vector<double> roots = root_finder(P);
    cout << endl;
    for (int j = n - 1; j >= 0; --j) {
        cout << "\nlambda_" << n - j << " = " << roots[j] << endl;
    }
   
}

// Леверье-Фадеев
void LF(double** f, const int n) {
    setlocale(LC_ALL, "Russian");
    cout << "\nSecond thread: " << GetCurrentThreadId() << endl;

    double** E = new2DArray(n);
    double** A = new2DArray(n);
    double** B = new2DArray(n);
    double p = 0;
    double** F = new2DArray(n);

    // единичная матрица
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            if (i == j) E[i][j] = 1;
            else E[i][j] = 0;
        }
    }

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            A[i][j] = f[i][j];
            if (i == j) p = p + A[i][j];

        }
    }

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            B[i][j] = A[i][j] - (p * E[i][j]);
        }
    }
    //print2DArray(B, n);
    //cout <<"\n" << p <<"\n";
    F[0][0] = p;
    p = 0;

    for (int k = 2; k <= n; k++) {
        A = MultiplyWithOutAMP(n, f, B);

        //print2DArray(A, n);

        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (i == j) p = p + A[i][j];
            }
        }

        p = p / k;
        // cout << "\n" << p << "\n";
        F[0][k - 1] = p;

        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                B[i][j] = A[i][j] - (p * E[i][j]);
            }
        }
        // print2DArray(B, n);
        p = 0;

    }

    cout << "\nLeverrier – Faddeev" << "\n\n";
    cout << "Frobenius (P)" << "\n";

    cout << "\n";
    vector<double> P(n + 1);
    P[n] = 1;
    int kb = 0;
    for (int j = n - 1; j >= 0; j--) {
        P[j] = -(F[0][kb]);
        kb++;
    }


    for (int j = 0; j < n; ++j)
        cout << F[0][j] << " ";

    vector<double> roots = root_finder(P);
    cout << "\n";
    for (int j = n - 1; j >= 0; --j) {
        cout << "\nlambda_" << n - j << " = " << roots[j] << endl;
    }
}
   
// транспонирование матрицы
double** newTransposeMatrix(double** matrix, const int n)
{
    double** res = new2DArray(n);

    for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
            res[j][i] = matrix[i][j];

    return res;
}

// метод Гаусса
void GAUSS(double** B, const int n) {

    double d, s;
    double* x = new double[n];
    for (int k = 0; k < n; k++) // прямой ход

    {

        for (int j = k + 1; j < n; j++)

        {

            d = B[j][k] / B[k][k]; // формула (1)

            for (int i = k; i < n; i++)

            {

                B[j][i] = B[j][i] - d * B[k][i]; // формула (2)

            }

            B[j][n] = B[j][n] - d * B[k][n]; // формула (3)

        }

    }

    for (int k = n - 1; k >= 0; k--) // обратный ход

    {

        d = 0;

        for (int j = k + 1; j < n; j++)

        {

            s = B[k][j] * x[j]; // формула (4)

            d = d + s; // формула (4)

        }

        x[k] = (B[k][n] - d) / B[k][k]; // формула (4)

    }

    // cout << "Korni sistemy: " << endl;

     //for (int i = 0; i < n; i++)

      //   cout << "x[" << i << "]=" << x[i] << " " << endl;

    vector<double> P(n + 1);
    P[n] = 1;
    int kb = 0;
    for (int j = n - 1; j >= 0; j--) {
        P[j] = -x[j];
        kb++;
    }

    cout << "\n";
    for (int j = n - 1; j >= 0; --j)
        cout << x[j] << " ";

    vector<double> roots = root_finder(P);
    cout << "\n";
    for (int j = n - 1; j >= 0; --j) {
        cout << "\nlambda_" << n - j << " = " << roots[j] << endl;
    }

}

// Крылов
void Wings(double** f, const int n) {
    setlocale(LC_ALL, "Russian");
    cout << "\nThird thread: " << GetCurrentThreadId() << endl;
    double** B = new2DArray(n + 1);
    for (int i = 0; i < n + 1; i++) {
        for (int j = 0; j < n + 1; j++) {
            B[i][j] = 0;
        }
    }

    B[0][0] = 1;

    for (int k = 1; k <= n; k++) {
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                B[i][k] = B[i][k] + f[i][j] * B[j][k - 1];
            }
        }
    }
    // print2DArray(B, n);

    for (int i = 0; i < 1; i++) {

        for (int j = 0; j <= n; j++) {
            if (B[0][0] != 1) {
                B[0][j] = B[0][j] / B[0][0];
            }
        }

        for (int j = 0; j <= n; j++) {
            if (B[i + 1][0] != 0) {
                B[i + 1][j] = B[i + 1][j] - B[i][j] * (B[i + 1][j]);
            }

        }
    }

    cout << "\nKrylov:" << "\n\n";
    print2DArray(B, n);
    cout << "\n";
    cout << "Frobenius (P)" << "\n";
    GAUSS(B, n);
}
    


DWORD WINAPI SecondThread(LPVOID lpParameter) {
    EnterCriticalSection(&g_cs);
    Params* pParams = (Params*)lpParameter;
    DAN(pParams->f, pParams->n);
    LeaveCriticalSection(&g_cs);
    return 0;
}

DWORD WINAPI ThirdThread(LPVOID lpParameter) {
    EnterCriticalSection(&g_cs);
    Params* pParams = (Params*)lpParameter;
    LF(pParams->f, pParams->n);
    LeaveCriticalSection(&g_cs);
    return 0;
}

DWORD WINAPI FourthThread(LPVOID lpParameter) {
    EnterCriticalSection(&g_cs);
    Params* pParams = (Params*)lpParameter;
    Wings(pParams->f, pParams->n);
    LeaveCriticalSection(&g_cs);
    return 0;
}

void printError(const TCHAR* msg)
{
    DWORD eNum;
    TCHAR sysMsg[256];
    TCHAR* p;

    eNum = GetLastError();
    FormatMessage(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
        NULL, eNum,
        MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), // Default language
        sysMsg, 256, NULL);

    // Trim the end of the line and terminate it with a null
    p = sysMsg;
    while ((*p > 31) || (*p == 9))
        ++p;
    do { *p-- = 0; } while ((p >= sysMsg) &&
        ((*p == '.') || (*p < 33)));

    // Display the message
    _tprintf(TEXT("\n  WARNING: %s failed with error %d (%s)"), msg, eNum, sysMsg);
}

int main()
{
    HANDLE hThread, hThread2, hThread3;
    InitializeCriticalSection(&g_cs);
    Params parameters;
    FILETIME ftKernelTime, ftUserTime, crTime, exitTime;
    __int64 time;
    setlocale(LC_ALL, "Russian");
    // вводим матрицу размеры матрицы 
    int n = 0;
    ifstream matfile("MATRIXPO.txt");
    matfile >> n;
    if (n < 1 || n>10) {
        cout << "Матрица должна быть размерности от 2 до 10!" << "\n";
    }
    else {
        cout << "\nDimension n = " << n << "\n";
        vector<vector<double>> def(n, vector<double>(n));

        // создаём новую матрицу nxn
        double** A = new2DArray(n);

        // заполняем 
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {

                matfile >> def[i][j];
            }
        }

        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                A[i][j] = def[i][j];

        // выводим
        cout << "\nMatrix\n";
        print2DArray(A, n);
        parameters = { A,n };
        int pr[3];
        for (int j = 0; j < 3; j++) {
            matfile >> pr[j];
        }
        cout << "DAN: " << pr[0] << "\n";
        cout << "\nLF: " << pr[1] << "\n";

        cout << "\nKR: " << pr[2] << "\n";

        float timp = 0;

        for (int bd = 1; bd < 4; bd++) {
            for (int i = 0; i < 3; i++) {
                if (pr[i] == bd) {
                    if (i == 0) {
                        hThread = CreateThread(NULL, // Атрибуты защиты по умолчанию
                            0, // Объем адресного пространства потока по умолчанию (1 Мб)
                            SecondThread, // Адрес функции, запускаемой в потоке
                            &parameters, // Параметры функции
                            NULL, // Запустить поток моментально
                            NULL); // ID-потока
                        WaitForSingleObject(hThread, INFINITE);
                        //CloseHandle(hThread);
                        GetThreadTimes(hThread, &crTime, &exitTime, &ftKernelTime, &ftUserTime);
                        time = getWorkTime(&crTime, &exitTime);
                        timp = timp + time;
                        cout << "\nFirst thread time: " << time << endl;
                    }
                    if (i == 1) {
                        hThread2 = CreateThread(NULL, // Атрибуты защиты по умолчанию
                            0, // Объем адресного пространства потока по умолчанию (1 Мб)
                            ThirdThread, // Адрес функции, запускаемой в потоке
                            &parameters, // Параметры функции
                            NULL, // Запустить поток моментально
                            NULL); // ID-потока
                        WaitForSingleObject(hThread2, INFINITE);
                        //CloseHandle(hThread2);
                        GetThreadTimes(hThread2, &crTime, &exitTime, &ftKernelTime, &ftUserTime);
                        time = getWorkTime(&crTime, &exitTime);
                        timp = timp + time;
                        cout << "\nSecond thread time: " << time << endl;
                    }
                    if (i == 2) {
                        hThread3 = CreateThread(NULL, // Атрибуты защиты по умолчанию
                            0, // Объем адресного пространства потока по умолчанию (1 Мб)
                            FourthThread, // Адрес функции, запускаемой в потоке
                            &parameters, // Параметры функции
                            NULL, // Запустить поток моментально
                            NULL); // ID-потока
                        WaitForSingleObject(hThread3, INFINITE);
                        //CloseHandle(hThread3);
                        GetThreadTimes(hThread3, &crTime, &exitTime, &ftKernelTime, &ftUserTime);
                        time = getWorkTime(&crTime, &exitTime);
                        timp = timp + time;
                        cout << "\nThird thread time: " << time << endl;
                    }
                }
            }
        }









        cout << "\nProcess time: " << timp<< endl;
        DeleteCriticalSection(&g_cs);
    }
    return 0;
}


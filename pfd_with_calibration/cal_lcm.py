from fractions import Fraction
import math
import statistics

def lcm_of_integers(a: int, b: int) -> int:
    """計算兩個整數的最小公倍數"""
    return abs(a * b) // math.gcd(a, b)

def lcm_of_fractions(x: Fraction, y: Fraction) -> Fraction:
    """
    計算兩個 Fraction 型態數字的最小公倍數
    1. 將 x 與 y 寫成最簡分數: x = a/b, y = c/d
    2. 計算分母的最小公倍數 L = lcm(b, d)
    3. 轉換成共同分母： n1 = a*(L/b), n2 = c*(L/d)
    4. 最小公倍數為： LCM(x,y) = lcm(n1, n2) / L
    """
    # 取得分母的最小公倍數 L
    L = lcm_of_integers(x.denominator, y.denominator)
    # 將 x 與 y 轉換到相同分母下
    n1 = x.numerator * (L // x.denominator)
    n2 = y.numerator * (L // y.denominator)
    # 計算兩個分子之最小公倍數
    lcm_numer = lcm_of_integers(n1, n2)
    return Fraction(lcm_numer, L)

def main():
    #try:
    #    T1_input = input("請輸入 T1 的週期 (單位: ns，可以是小數): ")
    #    T2_input = input("請輸入 T2 的週期 (單位: ns，可以是小數): ")
    #    # 將輸入轉成 Fraction 型態，直接接受字串輸入，像是 "0.1" 或 "100.5"
    #    T1 = Fraction(T1_input)
    #    T2 = Fraction(T2_input)
    #except Exception as e:
    #    print("輸入有誤，請輸入正確的數值。", e)
    #    return

    sync_cycle_list=[]
    for i in range(-100, 100):
        ref_clk_freq = str(10e6)   #hz
        fb_clk_freq  = str(10e6+i) #hz


        T1 = Fraction(ref_clk_freq)
        T2 = Fraction(fb_clk_freq)
        # 計算最小公倍數，即兩個時鐘重合的時間
        overlap_time = lcm_of_fractions(T1, T2)
        
        # 計算各自需要多少個週期後重合
        cycles_T1 = overlap_time / T1
        cycles_T2 = overlap_time / T2

        
        print("ref_clk_fre:{} fb_clk_freq:{} sync_cycle(ref_clk):{}".format(ref_clk_freq, 
                                                                           fb_clk_freq, 
                                                                           cycles_T1 ))
        sync_cycle_list.append(cycles_T1)
 
    print("\n/////// ANALYSIS RESULT ///////")
    print("MAX SYNC CYCLE: {}".format(max(sync_cycle_list)))
    print("MIN SYNC CYCLE: {}".format(min(sync_cycle_list)))
    print("AVG SYNC CYCLE: {}".format(float(statistics.mean(sync_cycle_list))))
    print("MDN SYNC CYCLE: {}".format(statistics.median(sync_cycle_list)))

if __name__ == '__main__':
    main()

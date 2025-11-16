# mathmatic_in_elementary_number_th


初等数论讲义的形式化证明 by lean

## 版本

使用的 lean4 版本为 v4.24.0-rc1


## Contents


### Ch1_Greatest_Common_Divisor

- [x] Ch1_1_Excat_Division
- [x] Ch1_2_Division_with_remainder
- [x] Ch1_3_Greatest_Common_Divisor
- [x] ch1_4_Bezout_Identity

### Ch2_Prime_Numbers

- [ ] ch2_1_Prime_numbers
- [x] Ch2_2_Prime_Number_Theorem
- [ ] Ch2_3_Fundamental _theoem_of_arithmetic
- [ ] Ch2_4_p-adic_valuation

### Ch3_Congruences

- [ ] Ch3_1_congruences
- [ ] Ch3_2_Wilson's_theorem
- [ ] Ch3_3_Euler's_theorem


## 形式化证明目标


证明目标选用 青岛大学 刘奎,杨炯老师的英文讲义


## 结构


1. 证明的主体部分在 MathmaticInElementaryNumberTh 中, 按照章节 ch 分类


## 细节


1. 讲义中使用的 `Definition`, 通常用 `def` 表示

2. 因为lean中用来陈述和证明数学命题的关键词 仅有 `theorem`, `lemma`, `example` 无法满足讲义中所使用的 `Proposition` `Corollary` `Theorem` 等需求, 故在证明过程中均用 `theorem` 表示. 而讲义中的 `Lemma`,以及讲义中未出现但是为了方便后续证明的小命题, 在证明过程中使用同名 `lemma` 表示

3. 在 mathlib 中 已有的部分基础命题, 统一使用 mathlib 中给的证明或命题表示

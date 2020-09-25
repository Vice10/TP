Завдання:
Визначити, чи є число N парним, чи ні, не використовуючи ф-ї div, mod, якщо N > 0.
## Програма мовою SIPL

begin
&ensp; R:=0;
&ensp; K:=0;
&ensp; while K < N do K:= K + 2;
&ensp; if K = N then R:=1 else skip
end

## Семантичний терм

Sem_P(V12)
###### NS_Prog

Sem_P(begin
R:=0; K:=0; while K < N do K:= K + 2; if K = N then R:=1 else skip end)
###### NS_Prog

Sem_S(R:=0; K:=0; while K < N do K:= K + 2; if K = N then R:=1 else skip )
###### NS_Stm_Seq

Sem_S(R:=0; K:=0)•Sem_S(while K < N do K:= K + 2; if K = N then R:=1 else skip)

###### NS_Stm_Seq

Sem_S(R:=0)•Sem_S(K:=0)•Sem_S(while K < N do K:= K + 2; if K = N then R:=1 else skip)

###### NS_Stm_As

AS$^R$(Sem_A(0))•Sem_S(K:=0)•Sem_S(while K < N do K:= K + 2; if K = N then R:=1 else skip)

###### NS_Stm_As

AS$^R$(Sem_A(0))•AS$^K$(Sem_A(0))•Sem_S(while K < N do K:= K + 2; if K = N then R:=1 else skip)

###### NS_A_Num

AS$^R$($\bar{0}$)•AS$^K$(Sem_A(0))•Sem_S(while K < N do K:= K + 2; if K = N then R:=1 else skip)

###### NS_A_Num

AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)•Sem_S(while K < N do K:= K + 2; if K = N then R:=1 else skip)

###### NS_Stm_Seq

AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)•Sem_S(while K < N do K:= K + 2)•Sem_S(if K = N then R:=1 else skip)

###### NS_Stm_Wh

AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)•WH(Sem_B(K < N), Sem_S(K:= K + 2))•Sem_S(if K = N then R:=1 else skip)

###### ***DEFINE NS_B_sm***

sem_B(a1 < a2) = S²(sm, sem_A(a1),sem_A(a2))
###### NS_B_sm

AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)•WH(S²(sm, sem_A(K),sem_A(N)), Sem_S(K:= K + 2))•Sem_S(if K = N then R:=1 else skip)

###### NS_A_Var

AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)•WH(S²(sm, K=>,sem_A(N)), Sem_S(K:= K + 2))•Sem_S(if K = N then R:=1 else skip)

###### NS_A_Var

AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)•WH(S²(sm, K=>,N=>), Sem_S(K:= K + 2))•Sem_S(if K = N then R:=1 else skip)

###### NS_Stm_As

AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)•WH(S²(sm, K=>,N=>), AS$^K$(K + 2))•Sem_S(if K = N then R:=1 else skip)

###### NS_A_Add

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, sem_A(K), sem_A(2))))•
Sem_S(if K = N then R:=1 else skip)

###### NS_A_Var

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, sem_A(2))))•
Sem_S(if K = N then R:=1 else skip)

###### NS_A_Num

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
Sem_S(if K = N then R:=1 else skip)

###### NS_Stm_If

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(Sem_B(K = N), Sem_S(R:=1), Sem_S(skip))

###### NS_B_eq

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(S²(eq, sem_A(K), sem_A(N)), Sem_S(R:=1), Sem_S(skip))

###### NS_A_Var

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(S²(eq, K=>, sem_A(N)), Sem_S(R:=1), Sem_S(skip))

###### NS_A_Var

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(S²(eq, K=>, N=>), Sem_S(R:=1), Sem_S(skip))

###### NS_Stm_As
AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(S²(eq, K=>, N=>), AS$^R$(Sem_A(1)), Sem_S(skip))

###### NS_A_Num

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(S²(eq, K=>, N=>), AS$^R$($\bar{1}$), Sem_S(skip))

###### NS_Stm_skip

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(S²(eq, K=>, N=>), AS$^R$($\bar{1}$), id)



## Обчислення семантичного терму

Вхідні дані: N=5
st=[N↦5]

##### Семантичний терм:

AS$^R$($\bar{0}$)•
AS$^K$($\bar{0}$)•
WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$)))•
IF(S²(eq, K=>, N=>), AS$^R$($\bar{1}$), id)

#### Обчислимо AS$^R$($\bar{0}$)•AS$^K$($\bar{0}$)

###### AF_AS

AS$^R$($\bar{0}$)([N↦5]) = [N↦5] ]▽[ [R↦0] = [N↦5, R↦0]

###### AF_AS
↦▽[
AS$^K$($\bar{0}$)([N↦5, R↦0]) = [K↦0]▽ [N↦5, R↦0] = [K↦0, N↦5, R↦0] = st$_0$

#### Обчислимо WH(S²(sm, K=>,N=>), AS$^K$(S²(add, K=>, $\bar{2}$))) за ормло AF_WH
[fb/S²(sm, K=>,N=>),
fs/AS$^K$(S²(add, K=>, $\bar{2}$)),
st$_0$/([K↦0, N↦5, R↦0])]

### 1 ітерація

##### fb(st$_0$)
###### AF_S
S²(sm, K=>,N=>)([K↦0, N↦5, R↦0]) =
= sm(K=>([K↦0, N↦5, R↦0]), N=>[K↦0, N↦5, R↦0]) = sm(0,5) = true

Отже, обчислюємо **st$_1$=fs(st$_0$)**
###### AF_AS
AS$^K$(S²(add, K=>, $\bar{2}$))([K↦0, N↦5, R↦0]) =
[K↦0, N↦5, R↦0]▽[K↦S²(add, K=>, $\bar{2}$)([K↦0, N↦5, R↦0])]=
[K↦0, N↦5, R↦0]▽[K↦(add, K=>([K↦0, N↦5, R↦0], $\bar{2}$)]=
[K↦0, N↦5, R↦0]▽[K↦add(0,2)]=
[K↦0, N↦5, R↦0]▽[K↦2]=
[K↦2, N↦5, R↦0]

Маємо, st$_1$=[K↦2, N↦5, R↦0]
Необхідна ще принаймні одна ітерація циклю AF_WH зі станом st$_1$

### 2 ітерація

##### fb(st$_1$)
###### AF_S
S²(sm, K=>,N=>)([K↦2, N↦5, R↦0]) =
= sm(K=>([K↦2, N↦5, R↦0]), N=>[K↦2, N↦5, R↦0]) = sm(2,5) = true

Отже, обчислимо **st$_2$=fs(st$_1$)**
###### AF_AS
AS$^K$(S²(add, K=>, $\bar{2}$))([K↦2, N↦5, R↦0]) =
[K↦2, N↦5, R↦0]▽[K↦S²(add, K=>, $\bar{2}$)([K↦2, N↦5, R↦0])]=
[K↦2, N↦5, R↦0]▽[K↦(add, K=>([K↦2, N↦5, R↦0], $\bar{2}$)]=
[K↦2, N↦5, R↦0]▽[K↦add(2,2)]=
[K↦2, N↦5, R↦0]▽[K↦4]=
[K↦4, N↦5, R↦0]

Маємо, st$_2$=[K↦4, N↦5, R↦0]
Необхідна ще принаймні одна ітерація циклю AF_WH зі станом st$_2$

### 3 ітерація

##### fb(st$_2$)
###### AF_S
S²(sm, K=>,N=>)([K↦4, N↦5, R↦0]) =
= sm(K=>([K↦4, N↦5, R↦0]), N=>[K↦4, N↦5, R↦0]) = sm(4,5) = true

Отже, обчислюємо **st$_3$=fs(st$_2$)**
###### AF_AS
AS$^K$(S²(add, K=>, $\bar{2}$))([K↦4, N↦5, R↦0]) =
[K↦4, N↦5, R↦0]▽[K↦S²(add, K=>, $\bar{2}$)([K↦4, N↦5, R↦0])]=
[K↦4, N↦5, R↦0]▽[K↦(add, K=>([K↦4, N↦5, R↦0], $\bar{2}$)]=
[K↦4, N↦5, R↦0]▽[K↦add(4,2)]=
[K↦4, N↦5, R↦0]▽[K↦6]=
[K↦6, N↦5, R↦0]

Маємо, st$_3$=[K↦6, N↦5, R↦0]
Необхідна ще принаймні одна ітерація циклю AF_WH зі станом st$_3$.

### 4 ітерація

##### fb(st$_3$)
###### AF_S
S²(sm, K=>,N=>)([K↦6, N↦5, R↦0]) =
= sm(K=>([K↦6, N↦5, R↦0]), N=>[K↦6, N↦5, R↦0]) = sm(6,5) = false

Таким чином, цикл завершено.

#### Обчислимо IF(S²(eq, K=>, N=>), AS$^R$($\bar{1}$), id)([K↦6, N↦5, R↦0]) за ралом AF_IF

[fb/S²(eq, K=>, N=>),
fs$_1$/AS$^R$($\bar{1}$),
fs$_2$/id,
st/[K↦6, N↦5, R↦0]]

##### fb(st)
###### AF_S
S²(eq, K=>, N=>)([K↦6, N↦5, R↦0])=
eq(K=>([K↦6, N↦5, R↦0]), N=>([K↦6, N↦5, R↦0]))=
eq(K=>6, N=>5) = false
За формулою AF_IF, маємо обчислити fs$_2$

##### fs$_2$(st)
###### AF_ID
id(st) = st = [K↦6, N↦5, R↦0]

Таким чином, стан [K↦6, N↦5, R↦0] є остаточним.

def myhash(m, lm):
    return hash(m)%lm

def gen_p(ls, lam):
    e = [0, 0, 0, 0]
    ll = 1
    for i in range(len(ls)):
        e[i] = lam/2
        while True:
            if ls[i]^e[i]>=2^(2*lam):
                # print(e[i])
                ll = ll*ls[i]^e[i]
                break
            else:
                e[i] += 1
    f = next_prime(ls[len(ls)-1])
    while True:
        p1 = ll*f+1
        p2 = ll*f-1
        if p1 in Primes():
            # print("+")
            p = p1
            break
        if p2 in Primes():
            # print("-")
            p = p2
            break
        f = next_prime(f)
    return e, f, p

def gen_D(p, D = 2):
    D = D + 1
    while True:
        if kronecker_symbol(-D,p)==-1 and mod(D,4)==3:
            return D
        D=D+1

def gen_supersingularEC(p, ls, e):
    if mod(p, 4)==3:
        E = EllipticCurve(GF(p), [0,0,0,-1,0])
    else:
        # print("ll = ", ll)
        D = 1
        # while True:
        D = gen_D(p, D)
        # print("D = ", D)
        H = hilbert_class_polynomial(-D)
        # print(H)
        js = H.roots(GF(p), multiplicities=False)
        F = GF(p)
        # print("js = ", js)
        j = js[0]
        # print("j = ", j)
        tmp = (4*(1728-j))
        A = F((27*j)*pow(tmp, -1, p))
        E = EllipticCurve(GF(p), [A, -A])
        # print("A = ", A)
    F.<a> = GF(p^2)
    ff = a.minpoly('x')
    K.<t> = GF(p^2, modulus=ff)
    EK=E.base_extend(K)
    N=EK.cardinality()
    ll = (ls[0]^e[0] * ls[1]^e[1] * ls[2]^e[2] * ls[3]^e[3])^2
    if N%ll:
        EK = EK.quadratic_twist()
        N = EK.cardinality()
        if N%ll:
            print("WARNING !!!")
            return None
    return EK

def gen_base_point(E, l, e):
    N=E.cardinality()
    F=E.base_field()
    # try:        
    c=ZZ(N/(l^e)^2)   
    while True:
        PP=E.random_point()
        P=c*PP   
        if P.order() == l^e:        
            PA=P
            return PA
    return None

def gen_bases(E, l, e):
    points = list()

    for i in range(len(l)):
        while True:
            # print("l^e =", l[i]^e[i])
            # print("N = ", E.cardinality())
            # print("N/(l^e)^2 = ", E.cardinality()/l[i]^e[i])
            P=gen_base_point(E,l[i],e[i])
            Q=gen_base_point(E,l[i],e[i])
            ee = E.random_point()
            # try:
            ee=P.weil_pairing(Q, ZZ(l[i]^e[i]))
            # except:
                # continue
            if ee^(l[i]^e[i])==1:            
                points.append([P, Q])
                break
    return points

def gen_kernel_coef(l, e):
    while True:
        n = randint(1, l^e)
        if mod(n, l^e) != 0:
            return n
        

# returns p, E, {P_r, Q_r}, {P_s, Q_s}, {P_v, Q_v}, {P_m, Q_m}, e, f
def Setup(ls, lam):
    # print("Scheme setup")
    es, f, p = gen_p(ls, lam)
    # print(ls, es, f, p, p^2)
    EK = gen_supersingularEC(p, ls, es)
    # print(EK)
    bases = gen_bases(EK, ls, es) #base points for R, S, V, M
    # print(bases)
    return p, EK, (bases[0][0], bases[0][1]), (bases[1][0], bases[1][1]), (bases[2][0], bases[2][1]), (bases[3][0], bases[3][1]), es, f


# returns pk_s, sk_s, pk_v, sk_v
# pk_s = E_s, phi_S(P_v), phi_S(Q_v), phi_S(P_m), phi_S(Q_m)
# sk_s = n_s
# pk_v = E_v, phi_v(P_m), phi_v(Q_m), phi_v(P_s), phi_v(Q_s), phi_v(P_r), phi_v(Q_r)
# sk_v = n_v
def KeyGen(EK, ls, es, P_r, Q_r, P_s, Q_s, P_v, Q_v, P_m, Q_m):
    #signer part
    # print(ls, es)
    n_s = gen_kernel_coef(ls[1], es[1])
    # print("n_s: ", n_s)
    phiS = EllipticCurveIsogeny(EK, P_s + n_s * Q_s) # not well, but ok for MVP
    E_s = phiS.codomain()
    
    #verifier part
    n_v = gen_kernel_coef(ls[2], es[2])
    # print("n_v: ", n_v)
    phiV = EllipticCurveIsogeny(EK, P_v + n_v*Q_v)
    E_v = phiV.codomain()

    return (((E_s, phiS(P_v), phiS(Q_v), phiS(P_m), phiS(Q_m)), n_s),((E_v, phiV(P_m), phiV(Q_m), phiV(P_s), phiV(Q_s), phiV(P_r), phiV(Q_r)), n_v)) 



def Blind(m, l_m, e_m, l_r, e_r, E_v, phi_v_Pr, phi_v_Qr, phi_v_Ps, phi_v_Qs, phi_v_Pm, phi_v_Qm):

    l_re = l_r^e_r


    hm = myhash(m, l_m^e_m)
    # print("HASH: ", hm)


    phiVM = EllipticCurveIsogeny(E_v, phi_v_Pm + hm * phi_v_Qm)
    E_vm = phiVM.codomain()
    r = randint(1, l_r^e_r)

    phi_vm_phi_v_Pr = phiVM(phi_v_Pr)
    phi_vm_phi_v_Qr = phiVM(phi_v_Qr)
    phi_vm_phi_v_Ps = phiVM(phi_v_Ps)
    phi_vm_phi_v_Qs = phiVM(phi_v_Qs)


    
    phiVMR = EllipticCurveIsogeny(E_vm, phi_vm_phi_v_Pr + r * phi_vm_phi_v_Qr)
    E_vmr = phiVMR.codomain()


    phi_vmr_phi_vm_phi_v_Ps = phiVMR(phi_vm_phi_v_Ps)
    phi_vmr_phi_vm_phi_v_Qs = phiVMR(phi_vm_phi_v_Qs)


    #ker phi = G, where G is finite subgroup of E. 
    #as G is cyclic, we can check if point is equals to
    # n*P+m*Q

    # Берем точку K из группы кручения кривой E_vm с порядком
    # l_r^e_r (ls[0]^es[0]), но не из ядра phiVMR, то есть 
    # эта точка не является одной из всех суммами точек 
    # P_r, Q_r.

    # Мы знаем E_vmr
    # Берем точку K_v на кривой E_vm, ord(K_v) = l^e
    # Проверяем, что phi_vmr(K_v) != 0
    # Строим phi_hat_vmr как E_vmr/phi_vmr(K_v)
    # Потом берем дву случайные точки на E_vmr порядка l^e (bases)
    # и находим такие m, n что mP'+nQ' = phi_vmr(K_v) <- вот тут проще джействовать наоборот, естественно.
    # 
    # Наоборот: находим две случайные точки, коэфициенты берем случайно, складываем
    # Получили phi_vmr(K_v) = mP'+nQ'
    # Потом строим phi_hat_vmr = E_vmr/phi_vmr(K_v)
    # проверяем, что phi_hat_vmr(phi_vmr(K_v)) имеет порядок ровно l^e. Если нет, то начинаем по-новой
     



    # while True:
    #     K_v = gen_base_point(E_vm, ls[0], es[0])
    #     if phiVMR(K_v)[0] == 0 and phiVMR(K_v) == 0:
    #         continue
    #     else:
    #         break
    K_v = gen_base_point(E_vm, l_r, e_r)
    while True:
        K_v = gen_base_point(E_vm, l_r, e_r)
        # K_v = E_vm.random_point()
        # print(K_v.order())
        if K_v.order() != l_r^e_r:
            continue
        # print(K_v, end="")
        if phiVMR(K_v).is_zero():
            # print(" in ker")
            continue
        else:
            break

    # cyclic_kernel = []
    # for i in range(K_v.order()):
    #     # print(i*phiVMR(K_v))
    #     cyclic_kernel.append(i*phiVMR(K_v))
    
    # print(len(cyclic_kernel))

    phi_hat_VMR = EllipticCurveIsogeny(E_vmr, phiVMR(K_v))

    # print(phi_hat_VMR, "js = ", phi_hat_VMR.codomain().j_invariant(), " ", phi_hat_VMR.domain().j_invariant())
    # print(phiVMR, "js = ", phiVMR.codomain().j_invariant(), " ", phiVMR.domain().j_invariant())
    # print(phiVMR.codomain() == phi_hat_VMR.domain())
    # print(phi_hat_VMR.codomain() == phiVMR.domain())

    E1 = phiVMR.codomain()
    E2 = phi_hat_VMR.domain()
    E3 = phi_hat_VMR.codomain()
    E4 = phiVMR.domain()


    j1 = E1.j_invariant()
    j2 = E2.j_invariant()
    j3 = E3.j_invariant()
    j4 = E4.j_invariant()

    # print("j1 = ", j1)
    # print("j2 = ", j2)
    # print("j3 = ", j3)
    # print("j4 = ", j4)

    if j3 != j4:
        E3 = E3.quadratic_twist()
        j3 = E3.j_invariant()

    # print("new j3 = ", j3)

    # tt = phiVMR.dual()
    # print(tt)
    



    # print(E_vm.torsion_subgroup())


    phiVMR_K_v = phiVMR(K_v)



    while True:
        while True:
            P_hatch_r = gen_base_point(E_vmr, l_r, e_r)
            Q_hatch_r = gen_base_point(E_vmr, l_r, e_r)
            
            ee = P_hatch_r.weil_pairing(Q_hatch_r, ZZ(l_r^e_r))
            if ee^(l_r^e_r) == 1:
                break
        # print(P_hatch_r.order(), Q_hatch_r.order())
        n = 0
        m = 0
        print(P_hatch_r, Q_hatch_r)
        while True:
            if m * P_hatch_r + n*Q_hatch_r == phiVMR_K_v:
                break
            m = m+1
            # print(m, n)
            if m > l_re:
                m = 0
                n = n+1
                # print(".",end="")
                if n>l_re:
                    print("NOTHING")
                    n = 0
                    m = 0
                    break
        if n != 0 or m != 0:
            break
        
        
    

    print(n, m)
    #     phi_VMR_K = m*P_hatch_r + n * Q_hatch_r
        

    #     phi_hat_vmr = EllipticCurveIsogeny(E_vmr, phi_VMR_K)

    #     K = gen_base_point(E_vm, l_r, e_r)
    #     print(K.order(), l_r^e_r, phi_VMR_K.order(), phi_hat_vmr(phi_VMR_K).order())
    #     if (K.order() != l_r^e_r):
    #         continue
        
    #     # print(phi_hat_vmr(phi_VMR_K).order(), l_r^e_r, phi_hat_vmr(phi_VMR_K) )

    #     if phi_hat_vmr(phi_VMR_K).order() == l_r^e_r:
    #         K_v = phi_hat_vmr(phi_VMR_K) 
    #         break





    return E_vmr, (P_hatch_r, Q_hatch_r), phi_vmr_phi_vm_phi_v_Ps, phi_vmr_phi_vm_phi_v_Qs, m, n, phi_hat_VMR




def Sign(E_vmr, phi_vmr_phi_vm_phi_v_Ps, phi_vmr_phi_vm_phi_v_Qs, n_s, P_hatch_r, Q_hatch_r):

    phi_vmrs = EllipticCurveIsogeny(E_vmr, phi_vmr_phi_vm_phi_v_Ps + n_s * phi_vmr_phi_vm_phi_v_Qs)
    E_vmrs = phi_vmrs.codomain()

    phi_vmrs_P_hatch_r = phi_vmrs(P_hatch_r)
    phi_vmrs_Q_hatch_r = phi_vmrs(Q_hatch_r)

    return E_vmrs, phi_vmrs_P_hatch_r, phi_vmrs_Q_hatch_r

def Unblind(E_vmrs, m, n, phi_vmrs_P_hatch_r, phi_vmrs_Q_hatch_r, phi_hat_vmr):
    phi_vmrsr_hatch = EllipticCurveIsogeny(E_vmrs, m*phi_vmrs_P_hatch_r + n * phi_vmrs_Q_hatch_r)
    E_vmrsr_hatch = phi_vmrsr_hatch.codomain()

    print("DEBUG")
    print("E_vmrsr_hatch_j", E_vmrsr_hatch.j_invariant())
    print("E_vmrsr_hatch_twisted_j", E_vmrsr_hatch.quadratic_twist().j_invariant())


    print("\n\n", phi_vmrsr_hatch ,"\n\n")

    return E_vmrsr_hatch.j_invariant()


def Verify(m, j_inv_E_vmrsr_hatch, l_m, e_m, E_s, phi_s_Pv, phi_s_Qv, phi_s_Pm, phi_s_Qm, n_v):

    hm = myhash(m, l_m^e_m)
    print("HASH: ", hm)


    phi_sv = EllipticCurveIsogeny(E_s, phi_s_Pv + n_v*phi_s_Qv)
    E_sv = phi_sv.codomain()

    phi_sv_phi_s_Pm = phi_sv(phi_s_Pm)
    phi_sv_phi_s_Qm = phi_sv(phi_s_Qm)

    phi_svm = EllipticCurveIsogeny(E_sv, phi_sv_phi_s_Pm + hm * phi_sv_phi_s_Qm)
    E_svm = phi_svm.codomain()

    print("DEBHUUUUG")
    print("j_inv on ver: ", E_svm.j_invariant())
    print("j_inv of quadratic_twist on ver: ", E_svm.quadratic_twist().j_invariant())
    print("exp: ", j_inv_E_vmrsr_hatch)

    if j_inv_E_vmrsr_hatch == E_svm.j_invariant():
        return True
    elif j_inv_E_vmrsr_hatch == E_svm.quadratic_twist().j_invariant():
        return True

    return False

    



def main():
    l = [2,3,5,7]
    lam = 32


    p, EK, (P_r, Q_r), (P_s, Q_s), (P_v, Q_v), (P_m, Q_m), e, f = Setup(l, lam)

    print("========== SETUP ==========")
    print("lam = ", lam)
    print("l = ", l)
    print("e = ", e)
    print("f = ", f)
    print("p = ", p)
    print("EK = ", EK) 
    print("P_r = ", P_r, P_r.order())
    print("Q_r = ", Q_r, Q_r.order())
    print("P_s = ", P_s, P_s.order())
    print("Q_s = ", Q_s, Q_s.order())
    print("P_v = ", P_v, P_v.order())
    print("Q_v = ", Q_v, Q_v.order())
    print("P_m = ", P_m, P_m.order())
    print("Q_m = ", Q_m, Q_m.order())


    ((pk_s, sk_s), (pk_v, sk_v)) = KeyGen(EK, l, e, P_r, Q_r, P_s, Q_s, P_v, Q_v, P_m, Q_m)
    

    E_s = pk_s[0]
    phi_s_Pv = pk_s[1]
    phi_s_Qv = pk_s[2]
    phi_s_Pm = pk_s[3]
    phi_s_Qm = pk_s[4]

    n_s = sk_s

    E_v = pk_v[0]
    phi_v_Pm = pk_v[1]
    phi_v_Qm = pk_v[2]
    phi_v_Ps = pk_v[3]
    phi_v_Qs = pk_v[4]
    phi_v_Pr = pk_v[5]
    phi_v_Qr = pk_v[6]

    n_v = sk_v


    print("========== KEYGEN ==========")
    print("======= pk_s =======")
    print("E_s = ", E_s)
    print("phi_s_Pv = ", phi_s_Pv)
    print("phi_s_Qv = ", phi_s_Qv)
    print("phi_s_Pm = ", phi_s_Pm)
    print("phi_s_Qm = ", phi_s_Qm)
    print("======= sk_s =======")
    print("n_s = ", n_s)
    print("======= pk_v =======")
    print("E_v = ", E_v)
    print("phi_v_Pm = ", phi_v_Pm)
    print("phi_v_Qm = ", phi_v_Qm)
    print("phi_v_Ps = ", phi_v_Ps)
    print("phi_v_Qs = ", phi_v_Qs)
    print("phi_v_Pr = ", phi_v_Pr)
    print("phi_v_Qr = ", phi_v_Qr)
    print("======= sk_v =======")
    print("n_v = ", n_v)
    

    mess = "Hello world"
    fake_mess = "Hello w0rld"

    E_vmr, (P_hatch_r, Q_hatch_r), phi_vmr_phi_vm_phi_v_Ps, phi_vmr_phi_vm_phi_v_Qs, m, n, phi_hat_vmr = Blind(mess, l[3], e[3], l[0], e[0], E_v, phi_v_Pr, phi_v_Qr, phi_v_Ps, phi_v_Qs, phi_v_Pm, phi_v_Qm)


    print("========== SIGN ==========")
    print("======= Blinding =======")
    print("E_vmr = ", E_vmr)
    print("P'_r = ", P_hatch_r)
    print("Q'_r = ", Q_hatch_r)
    print("phi_vmr_phi_vm_phi_v_Ps = ", phi_vmr_phi_vm_phi_v_Ps)
    print("phi_vmr_phi_vm_phi_v_Qs = ", phi_vmr_phi_vm_phi_v_Qs)
    print("m = ", m)
    print("n = ", n)
    print("phi_hat_vmr = ", phi_hat_vmr)

    E_vmrs, phi_vmrs_P_hatch_r, phi_vmrs_Q_hatch_r = Sign(E_vmr, phi_vmr_phi_vm_phi_v_Ps, phi_vmr_phi_vm_phi_v_Qs, n_s, P_hatch_r, Q_hatch_r)

    print("======= Signing =======")
    print("E_vmrs = ", E_vmrs)
    print("phi_vmrs_P'_r = ", phi_vmrs_P_hatch_r)
    print("phi_vmrs_Q'_r = ", phi_vmrs_Q_hatch_r)


    j_inv_E_vmrsr_hatch = Unblind(E_vmrs, m, n, phi_vmrs_P_hatch_r, phi_vmrs_Q_hatch_r, phi_hat_vmr)

    print("======= Unblinding =======")
    print("j_inv = ", j_inv_E_vmrsr_hatch)
    


    true_result = Verify(mess, j_inv_E_vmrsr_hatch, l[3], e[3], E_s, phi_s_Pv, phi_s_Qv, phi_s_Pm, phi_s_Qm, n_v)

    false_result = Verify(fake_mess, j_inv_E_vmrsr_hatch, l[3], e[3], E_s, phi_s_Pv, phi_s_Qv, phi_s_Pm, phi_s_Qm, n_v)

    print("========== VERIFY ==========")
    print("Expected true = ", true_result)
    print("Expected false = ", false_result)











    









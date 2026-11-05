import YM.Nonperturbative.Headlines
import YM.Next.FOUNDATIONS.SU2
import YM.Gauge.Lie

/-! Concrete application of the combined Wilson existence theorem to SU(2).
The matrices below span its real Lie algebra. Their commutators show that any
nonzero ideal contains all three. -/
set_option autoImplicit false
noncomputable section
namespace YM.Examples.SU2
open Matrix Function Filter NormedSpace Asymptotics Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical ComplexOrder

private abbrev M := Matrix (Fin 2) (Fin 2) ℂ
private abbrev G:= SUtwo
private abbrev A : M:= !![Complex.I,0;0,-Complex.I]
private abbrev B : M:= !![0,1;-1,0]
private abbrev C : M:= !![0,Complex.I;Complex.I,0]

private lemma lies (X:M) (hh:star X = -X)(ht:X*X= -(1:M))
    (h:∀ (c s:ℝ),s^2+c^2=1 → det (c • (1:M)+s • X)=1) : X∈ G.lie:= by
    let f(z:ℝ): M:= Real.cos z • (1:M)+ Real.sin z • X
    have hF : HasDerivAt f X 0:= by
        have hh:= ((Real.hasDerivAt_cos 0).smul_const (1:M)).add ((Real.hasDerivAt_sin 0).smul_const X); simpa using! hh
    refine G.tangent_generates (f:=f) hF (by change f 0 = (1:M); simp [f]) fun t=>?_
    let s:= Real.sin t; let c:= Real.cos t; have he:s^2+c^2=1:=Real.sin_sq_add_cos_sq t
    have hz: f t ∈ unitary M:= by
        apply Matrix.mem_unitaryGroup_iff.mpr
        change (c • (1:M)+ s • X) * star (c • (1:M)+ s • X)= _
        rw [star_add,star_smul,star_smul,star_one, hh]; simp_rw [star_trivial]; rw [mul_add,add_mul,add_mul, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,smul_mul_smul_comm,one_mul,one_mul,mul_one,mul_neg,ht];
        rw[neg_neg];
        conv_rhs=> rw [← one_smul ℝ (1:M),← he]
        module
    let x : GaugeU G.n := ⟨f t,hz⟩; have hx:x∈ G.imageGroup:= h c s he
    exact ⟨⟨x,hx⟩,rfl⟩

local macro "entry" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_eq_conjTranspose, Complex.star_def,A,B,C,Matrix.mul_apply,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im, Complex.neg_im]))
private lemma a_in : A∈ G.lie:=by
   apply lies (X:=A)
   · entry
   · entry
   intro c s he; rw [Matrix.det_fin_two]; norm_num [A,Complex.real_smul]; ring_nf; simp; exact_mod_cast ((add_comm (c^2) _).trans he : c^2+s^2=1)
private lemma b_in:B∈ G.lie:=by
   apply lies (X:=B)
   · entry
   · entry
   intro c s he; rw [Matrix.det_fin_two]; norm_num [B,Complex.real_smul];ring_nf; norm_cast; linarith only[he]
private abbrev comm(x y:M):M:=x*y-y*x
private lemma ab : comm A B=(2:ℝ) • C:=by unfold comm;rw [two_smul];entry
private lemma bc : comm B C=(2:ℝ) • A:=by unfold comm;rw [two_smul];entry;ring
private lemma ca : comm C A=(2:ℝ) • B:=by unfold comm;rw [two_smul];entry;ring
private lemma negs(x y:M): comm y x= -comm x y:=by unfold comm; abel
private lemma comb(x y z:M)(t:ℝ)(s:ℝ)(u:ℝ)(v : M) : comm x (t • y+s • z+u • v)=t • comm x y+s • comm x z+u • comm x v:=by unfold comm; simp only [add_mul,mul_add,smul_mul_assoc, mul_smul_comm,smul_sub]; abel
private lemma drank {L:Submodule ℝ M}{x:M}{c:ℝ}(h:c • x∈L)(he:c≠0):x∈L:=by simpa only[smul_smul,inv_mul_cancel₀ he,one_smul] using L.smul_mem c⁻¹ h
private lemma c_in:C∈ G.lie:=drank (c:=2) (ab ▸ (show comm A B∈G.lie from G.bracket_mem a_in b_in)) (by norm_num)

private lemma trzero(X:M)(ht:X∈ G.lie): X 0 0+X 1 1=0:=by
    let f(t:ℝ):= NormedSpace.exp (t • X)
    have hV:HasDerivAt f X 0:=by simpa only[zero_smul,NormedSpace.exp_zero,one_mul] using! hasDerivAt_exp_smul_const X (0:ℝ)
    have hv(t:ℝ):det (f t)=1:=by
        obtain ⟨q,hp⟩:= (show G.Generates X from ht) t
        change G.mat q=f t at hp; rw[← hp]; exact q.property
    have hh(i j:Fin 2):HasDerivAt (fun t=> f t i j) (X i j) 0:=by
        let A : M →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun y=> y i j, map_add':=fun _ _ => rfl, map_smul':=fun _ _=> rfl }
        exact A.hasFDerivAt.comp_hasDerivAt _ hV
    have hz:= ((hh 0 0).mul (hh 1 1)).sub ((hh 0 1).mul (hh 1 0));
    have hH: HasDerivAt (fun t=> det (f t)) _ 0 := hz.congr_of_eventuallyEq (Eventually.of_forall (fun t=> Matrix.det_fin_two ..))
    simp_rw [hv] at hH; simpa only [show f 0=(1:M) by simp [f],Matrix.one_apply, ite_true, show ¬(1:Fin 2)=0 from by decide, show ¬(0:Fin 2)=1 from by decide, ite_false, zero_mul,mul_zero,one_mul,mul_one,sub_zero, zero_add, ↓reduceIte] using hH.unique (hasDerivAt_const ..)
private lemma express(X:M)(ht:X∈ G.lie):∃ a b c:ℝ, X=a • A+b • B+c • C:=by
    have he:= trzero X ht
    let a:=(X 0 0).im; let b:=(X 0 1).re; let c:=(X 0 1).im; refine ⟨a,b,c,?_⟩
    have hp(x y:Fin 2): (star (X y x))= -(X x y):= congr_fun (congr_fun (G.generates_skew ht) x) y
    have hX: (X 1 1)= -(X 0 0):= (neg_eq_iff_add_eq_zero.mpr he).symm
    have hY:(X 1 0)= -(star (X 0 1)):=by rw [hp,neg_neg]
    have hz: (X 0 0).re=0:=by have hu:=congr_arg Complex.re (hp 0 0); simp only [Complex.star_def,Complex.conj_re,Complex.neg_re] at hu;linarith only[hu]
    ext i j;fin_cases i<;> fin_cases j<;> simp [A,B,C,Complex.real_smul,hX,hY,a,b,c]<;> apply Complex.ext<;> simp[hz]

/-- The defining representation of SU(2) has nonabelian simple real Lie algebra. -/
theorem simple : SUtwo.Simple :=by
    refine ⟨⟨A,a_in,B,b_in,?_⟩,?_⟩
    · change comm A B≠0; rw [ab]; refine smul_ne_zero (by norm_num:(2:ℝ)≠0) fun he=>?_; have hx:= congr_fun (congr_fun (show C=(0:M) from he) 0) 1; exact Complex.I_ne_zero hx
    intro X h ht
    by_cases hx:X=⊥; exact Or.inl hx
    obtain ⟨v,hv,hP⟩:= (Submodule.ne_bot_iff ..).mp hx
    obtain ⟨a,b,c,hC⟩:= express v (h hv); subst v
    have hab : A∈X → (A∈X∧B∈X∧C∈X):= fun x=> ⟨x,drank (ca ▸ (show comm C A∈ X from ht C c_in A x)) (by norm_num), drank (c:= -2) (by rw [neg_smul,← ab,← negs];exact ht _ b_in _ x) (by norm_num)⟩
    have W(w:M)(hw:w∈G.lie)(v:M)(h:v∈X): v + (1/4:ℝ) • comm w (comm w v) ∈ X:= X.add_mem h (X.smul_mem _ (ht _ hw _ (ht _ hw _ h)))
    have hu (U V W' : M)(hU:U∈G.lie)(he:comm U V=(2:ℝ) • W')(he':comm W' U=(2:ℝ) • V)(v:ℝ)(hV:v ≠0)(x y:ℝ)(hz:v • U+x • V+y • W'∈ X): U∈X:=by
        have hx:= W U hU _ hz
        rw [comb U U V v x y W',show comm U U=0 from sub_self _, he,negs W',he'] at hx
        rw [show v • (0:M)+x • ( (2:ℝ) • W')+y • (-( (2:ℝ) • V))=(0:ℝ) • U+(x*2) • W'+(-y*2) • V from by module] at hx
        rw[comb,show comm U U=0 from sub_self _,negs W', he, he'] at hx
        refine drank (c:=v) ?_ hV
        have he:v • U+x • V+y • W'+ (1/4:ℝ) • ((0:ℝ) • (0:M)+(x*2) • (-( (2:ℝ) • V))+(-y*2) • ( (2:ℝ) • W'))=v • U:=by module
        rwa[he] at hx
    have hp:A∈X:=by
        by_cases hB:a=0
        swap; · exact hu A B C a_in ab ca a hB b c hv
        by_cases hb:b=0
        swap; · have hy: B∈X:= hu B C A b_in bc ab b hb c a (by rw[add_comm, ← add_assoc]; exact hv)
                exact drank (c:= -2) (by rw [neg_smul,← bc, ← negs]; exact ht _ c_in _ hy) (by norm_num)
        have hc:c≠0:=fun h=> hP (by rw[hB,hb,h]; simp;rfl)
        have hy: C∈X:= hu C A B c_in ca bc c hc a b (by rw[add_assoc,add_comm _ (_+_)]; exact hv)
        exact drank (bc ▸ (show comm B C∈ X from ht _ b_in _ hy)) (by norm_num)
    obtain ⟨hA,hB,hC⟩:= hab hp
    refine Or.inr (le_antisymm h (fun x hx=>?_)); obtain ⟨a,b,c,h⟩:= express x hx; rw[h]; exact X.add_mem (X.add_mem (X.smul_mem a hA) (X.smul_mem b hB)) (X.smul_mem c hC)

/-- All joint conclusions for SU(2) at unit blocking-kernel penalty. -/
theorem existence : Nonperturbative.Headline.WilsonExistence.{0,0} SUtwo simple 1 :=
  Nonperturbative.existence SUtwo simple 1 zero_lt_one

end YM.Examples.SU2

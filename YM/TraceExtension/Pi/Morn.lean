import YM.TraceExtension.Pi.Mantle
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory
open Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Interval Classical InnerProductSpace
variable {G:Gauge}{n:Side}{F:Peat G n}{P:Support n}
section Song
open Complex
abbrev pulseB (p:Track)(i:Axis)(j:Lines G n 1):= midV p i (Place.seat (lift j.1))
variable (i: Axis)(a:G.ColorIndex)(F:Peat G n)
abbrev cashB (j:Lines G n 1):ℂ:= (Pi.single (M:=fun _=> ℂ) (mood G i a) 1) j.2
def wisp (n:Side)(p:Track): Phase (Lines G n 1):= Complex.exp (Complex.I * (p i:ℂ)/2) • barca (0:Site n) p (mood G i a)
lemma wisp_at (j:Lines G n 1)(p:Track) : wisp i a n p j=Complex.exp (↑(pulseB p i j)*Complex.I)* cashB i a j:=by
    unfold wisp cashB barca; simp only [Pi.smul_apply,smul_eq_mul,← mul_assoc]; rw [show Laurent.mode _ _=_ from rfl]; unfold mode; rw [← Complex.exp_add]; unfold pulseB midV; congr 2; rw[mind_t]; simp only [axes,Place.seat_apply, sub_zero]; push_cast; ring
lemma pulse_scale (p:Track)(j:Lines G n 1)(t:ℝ): pulseB (t • p) i j=t*pulseB p i j:=by unfold pulseB midV; simp_rw [mind_t]; simp only[Pi.smul_apply, smul_eq_mul,mul_add, Finset.mul_sum, mul_assoc];ring
lemma standU (j:Lines G n 1)(d:ℕ)(p:Track): cashB i a j * (pulseB p i j:ℂ)^d= axes (XR (n:=n) p i a d) j:=by
    rcases j with ⟨x,g,k⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective g
    change cashB i a (x,coord b,k)* _=Complex.ofReal (edgeColor (XR p i a d) (x,b) k)
    have he: edgeColor (XR (n:=n) p i a d)=_ := edgeColor.apply_symm_apply _; rw[he]; unfold cashB elimA mood; dsimp only; rw[sub_zero]; by_cases h:i=b <;> by_cases hh:k=a <;> simp [Pi.single_apply, *,pulseB,basis_eq,coord_iff,midV]
abbrev aper(x:Land):ℂ:= Complex.exp (Complex.I * (x 0 i + x 1 i:ℝ)/2)
def mush (x:Land):ℂ:= beat (F ∘ input G n) 0 2 ![wisp i a n (x 0),wisp i a n (x 1)]
abbrev colM : Land→ℂ:= molt (0:Site n) ![mood G i a,mood G i a] (F ∘ input G n)
lemma aimed (x:Land) : mush i a F x = aper i x * colM i a F x:=by
    let A j:=barca (0:Site n) (x j) (mood G i a);let Z(j):=Complex.exp (Complex.I*(x j i:ℂ)/2)
    rw [mush, show (![wisp i a n (x 0),wisp i a n (x 1)]:Fin 2→_)=fun j=> Z j • A j from funext fun j=>by fin_cases j<;>rfl,MultilinearMap.map_smul_univ,Fin.prod_univ_two,smul_eq_mul,colM,molt_be]
    congr 1
    · unfold Z aper; rw[← Complex.exp_add]; push_cast; ring_nf
    congr 1; funext k; fin_cases k<;>rfl
lemma exp_lead(x:ℂ)(n:ℕ)(c:ℂ): neap n (fun t:ℝ=>Complex.exp (↑t*x)*c) 0 1=((n.factorial:ℂ)⁻¹)*x^n*c:=by
    have he(t:ℝ): HasDerivAt (fun t:ℝ=>Complex.exp (↑t*x)) (Complex.exp (↑t*x)*x) t:=by
        have ht: HasDerivAt (fun t:ℝ=>Complex.exp (↑t*x)) _ t := (Complex.hasDerivAt_exp _).comp t ((Complex.ofRealCLM.hasFDerivAt (x:=t)).hasDerivAt.mul_const x)
        apply Eq.mp _ ht; congr 1; simp
    have H(n:ℕ)(t:ℝ): iteratedDeriv n (fun t:ℝ=> Complex.exp (↑t*x)*c) t=Complex.exp (↑t*x)*x^n*c:=by
       induction n generalizing t with
       | zero=> simp
       | succ n ih=> rw[iteratedDeriv_succ, funext ih]; rw[show deriv _ _=_ from (((he t).mul_const (x^n)).mul_const c).deriv,pow_succ];ring
    rw[neap_der,H];simp [mul_assoc]
abbrev wash(x:Land)(j k:Lines G n 1):ℂ:= I*↑(pulseB (x 0) i j + pulseB (x 1) i k)
abbrev setM (j k:Lines G n 1):ℂ:= cashB i a j *Kane F j k* cashB i a k
lemma expo (x:Land): mush i a F x=∑ j:Lines G n 1, ∑ k:Lines G n 1, Complex.exp (wash i x j k)*setM i a F j k:=by
   unfold mush; rw[stiff_body]; unfold Matrix.mulVec dotProduct; refine sum_congr rfl fun j _=>?_ ; rw [Finset.mul_sum]; refine sum_congr rfl fun k _=>?_ ; rw[wisp_at,wisp_at]; unfold wash; rw [Complex.ofReal_add (pulseB (x 0) i j) (pulseB (x 1) i k),mul_add,Complex.exp_add]; simp_rw [mul_comm Complex.I]; unfold setM; ring
lemma exp_run (d:ℕ)(x:Land): neap d (mush i a F) 0 x=∑ j:Lines G n 1,∑ k:Lines G n 1, ((d.factorial:ℂ)⁻¹)*(wash i x j k)^d*setM i a F j k:=by
   have hs(j k:Lines G n 1)(x:Land): ContDiffAt ℝ ω (fun z:Land=> Complex.exp (wash i z j k)*setM i a F j k) x:=by
      have hx(a:Fin 2)(j:Lines G n 1): ContDiff ℝ ω (fun z:Land=> pulseB (z a) i j):=by unfold pulseB midV; simp_rw [mind_t]; fun_prop
      unfold wash; have hr:= hx 0 j|>.add (hx 1 k); exact ((show ContDiff ℝ ω (fun z:Land=> Complex.exp (Complex.I * ↑(pulseB (z 0) i j+pulseB (z 1) i k))) from ContDiff.comp (contDiff_exp (𝕜:=ℝ)) ((Complex.ofRealCLM.contDiff.comp hr).const_smul Complex.I)).contDiffAt.mul contDiffAt_const)
   rw [funext (expo i a F)]; apply (neap_sumE (k:=d) x (h:=fun j _=> ContDiffAt.sum (fun k _=> hs j k _))).trans; apply sum_congr rfl fun j _=>?_
   rw [neap_sumE _ (fun k _=> hs j k 0)]; refine sum_congr rfl fun k _=>?_ ; rw [← chord_n _ _ _ (hs j k 0)]; rw[show (fun s:ℝ=>_)=(fun s:ℝ=> Complex.exp (↑s* wash i x j k)*setM i a F j k) from funext (fun i' => by
       simp only[zero_add,wash,Pi.smul_apply,pulse_scale]; push_cast;ring_nf), exp_lead]
end Song
end YM.Trace.Kits

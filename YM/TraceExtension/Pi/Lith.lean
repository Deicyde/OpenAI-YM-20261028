import YM.TraceExtension.Pi.Liken
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}{n:Side}{F:Peat G n}{P:Support n}{v:Label G 5}{H: Hol G}
open Complex
variable (d i b:Axis)(a:G.ColorIndex)
-- implement rho before quotient for any vectors
abbrev roseU (p q:Track): Jet G:=
    Pi.single 0 (Xtune p i (EuclideanSpace.basisFun G.ColorIndex ℝ a))+Pi.single 1 (Ytune q i (EuclideanSpace.basisFun G.ColorIndex ℝ a))
-- j symbol orientation
def unitK (J:Jet G) : Label G 5→ₗ[ℂ] ℂ:= (Labels.read J).toLinearMap ∘ₗ tier 5 ∘ₗ (localFields G 5).subtype
def lotR (x:Land) : Label G 5→ₗ[ℂ]ℂ:= (- Complex.I* (1/2:ℂ)) • (unitK (roseU i a (x 1) (x 0))+unitK (roseU i a (x 0) (x 1)))
@[simp] lemma rose_in(p q:Track): roseU i a p q 0=Xtune p i (EuclideanSpace.basisFun G.ColorIndex ℝ a):=by simp[roseU]
@[simp] lemma rose_out(p q:Track): roseU i a p q 1=Ytune q i (EuclideanSpace.basisFun G.ColorIndex ℝ a):=by simp[roseU]
lemma lot_ht (h:Cleric F)(hp: LocalOn P F)(hs: Nonwrapping P 0)(hn:2 ≤ n.val)(hG:G.Simple)(hx:JetTest H 0 v (Complex.ofRealCLM ∘ F))(x:Land): neap 3 (mush i a F) 0 x=lotR i a x v :=by
   rw [cold3 _ _ h hp hs hG hn]; unfold lotR; simp only[unitK,_root_.smul_apply,_root_.add_apply,LinearMap.comp_apply]; push_cast
   change _*(↑(sheen F _ _) + ↑(sheen F _ _))= (_:ℂ)*(Labels.read _ _ + Labels.read _ _); congr 2
   · have ht:= stamp5 h hG hx le_rfl (roseU i a (x 1) (x 0)); rw [rose_in,rose_out] at ht;exact ht.symm
   have ht:= stamp5 h hG hx le_rfl (roseU i a (x 0) (x 1)); rw [rose_in,rose_out] at ht;exact ht.symm
abbrev lag(d i b:Axis)(a:G.ColorIndex): Label G 5 →ₗ[ℂ] ℂ:= Deb ∘ₗ LinearMap.pi (fun x=> lotR i a (lawn d b x))
def termQ (d i b:Axis)(a:G.ColorIndex): (Axis→Label G 5)→ₗ[ℂ] ℂ:= lag d i b a ∘ₗ LinearMap.proj b
def archK (a:G.ColorIndex): (Axis→Label G 5)→ₗ[ℂ] ℂ:=∑ d,∑ i,(if d=i then 0 else ∑ b, termQ d i b a)
lemma arch_pay(a:G.ColorIndex)(x:Axis→ Label G 5): archK a x= suite (fun d i=>∑ b:Axis, lag d i b a (x b)):=by
   unfold archK; simp_rw [LinearMap.sum_apply]; unfold suite; apply sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; split_ifs with h
   · rfl
   rw[LinearMap.sum_apply];rfl
lemma clothK(a:G.ColorIndex)(x:Axis→ Peat G n)(v:Axis→ Label G 5)(h:∀ i, Cleric (x i))(hp:∀ i, LocalOn P (x i))(hs:Nonwrapping P 0)(hG:G.Simple)(hn:2 ≤ n.val)(hx:∀ i,JetTest H 0 (v i) (Complex.ofRealCLM ∘ x i)):
    Holt a (fun i=> x i∘ input G n)=archK a v:=by rw [Kits.height a hs hG hn x h hp, arch_pay]; congr 1; ext1 d; ext1 i;exact sum_congr rfl fun b _=> congr_arg Deb (funext fun t=>lot_ht i a (h b) (hp b) hs hn hG (hx b) _)
open Complex
variable (S:Signed)
lemma tier_turn (p:Label G 5)(J:Jet G) (s : Signed): unitK (G:=G) J (tensor s.ortho p) = unitK (axesMove (fun i=>Taylor.turn s.ortho⁻¹) J) p:=by
    apply smul_right_injective ℂ (r:= ((Nat.factorial 5):ℝ)) (by positivity)
    change _ • Labels.read J (tier 5 (tensor s.ortho p).val)= _ • Labels.read _ (tier 5 p.val); rw[← deriv_read, ← deriv_read]; apply congr_arg (fun f:ℝ→ℂ => iteratedDeriv 5 f 0); funext t; change Labels.read (scaleJet J t) (changed _ p.val)=_
    rw[eval_changed]; congr 2; ext1 i; exact Taylor.turn s.ortho⁻¹|>.map_smul (t^(i+2)) _
lemma tier_neg (p:Label G 5)(J:Jet G)(h:G.Simple): unitK (-J) p=unitK J p:=by
   obtain ⟨B,hx,he,H⟩:=low le_rfl p; have hp:= Low.linear_invariant h (Low.covariance hx H)
   apply smul_right_injective ℂ (r:= ((Nat.factorial 5):ℝ)) (by positivity); change _ • Labels.read (-J) (tier 5 p.val)= _ • Labels.read J (tier 5 p.val); rw[← deriv_read,← deriv_read]; refine congr_arg (fun f:ℝ→ℂ=> iteratedDeriv 5 f 0) (funext fun t=>?_); simp only [H,Low.eval,hp,map_neg,scaleJet,Pi.neg_apply,smul_neg,neg_neg,zero_add,add_zero,LinearMap.zero_apply,LinearMap.neg_apply]
lemma Xtune_r (p:Track)(v:G.Color): Xtune (S.act p) (S.perm i) v = (sign S i) • Taylor.turn S.ortho (Xtune p i v):=by
   unfold Xtune; rw [← Equiv.sum_comp S.perm,map_sum, Finset.smul_sum]; apply sum_congr rfl fun j _=>?_; rw[map_smul,S.act_at,turn_leg0]; unfold sign; split_ifs<;> module
lemma Ytune_r(p:Track)(v:G.Color): Ytune (S.act p) (S.perm i) v= sign S i • Taylor.turn S.ortho (Ytune p i v):=by
   unfold Ytune; rw [← Equiv.sum_comp S.perm,map_sum,Finset.smul_sum]; refine sum_congr rfl fun j _=>?_ ; rw[← Equiv.sum_comp S.perm, map_sum,Finset.smul_sum]; refine sum_congr rfl fun k _=>?_ ; rw[map_smul,S.act_at,S.act_at, turn_leg1]; unfold sign; split_ifs<;> module
lemma roseR (p q:Track)(v:Label G 5)(h:G.Simple): unitK (roseU (S.perm i) a (S.act p) (S.act q)) (tensor S.ortho v)=unitK (roseU i a p q) v:=by
    rw [tier_turn v _ S,show axesMove _ _=(sign S i) • roseU i a p q from ?_]
    · unfold sign; split
      · change unitK ((-1:ℝ) • _) v= _; rw [ show ((-1:ℝ) • roseU i a p q : Jet G) = -roseU i a p q from funext fun j=> neg_one_smul ℝ ((roseU i a p q) j) , tier_neg v _ h]
      rw [one_smul]
    let U:= EuclideanSpace.basisFun G.ColorIndex ℝ a
    have ht {k:ℕ}(x:Taylor G k):Taylor.turn S.ortho⁻¹ (sign S i • Taylor.turn S.ortho x)= sign S i • x:=by rw[map_smul,← Taylor.turn_mul, inv_mul_cancel,Taylor.oneTurn]
    ext1 k; unfold axesMove roseU; rw [Xtune_r,Ytune_r]; by_cases he:k=0
    · subst k; simp[ht]
    by_cases h1:k=1; · subst k; simp [ht]
    simp [Pi.single_eq_of_ne, *,ht]
end YM.Trace.Kits

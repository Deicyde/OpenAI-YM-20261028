import YM.R2I.Wind.Surface
/-!
# Threshold for winding

Minimal wound A price. M*=0 on small n impossibility. after-L height toll, uniform for ALL real Mesh volumes above minimum. We don't turn n into ∞ or assume Nonwrapping for coming A!
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Averaging.Wind
open Function Filter Set Lattice Wilson RG StressFlux Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
open PhysicalNext.Repeat Collection Anchor Next.Foundations
open Next.Scheduling Quotes RG.Supply Push.AbsoluteSums Footprint
variable {G:Gauge}{n:Side}{P:BudgetPoint}{X:Support n}{f:Pot G n}{a b:ℝ}{R:Listing G n}{F:Collection.Source G n}{t w:ℝ}
variable {B:ℕ}
def Wound (X : RegularAddress n) := ¬ Nonwrapping X.support X.site
lemma beyond (hn:20<n.val) : ∃ X:RegularAddress n,Wound X:= by
   use ⟨0,univ,mem_univ _⟩; let a:= step 0 (S:=ℤ); let k:=n.val/2
   let U:= k•a; let V:= wrap n U; let X:RegularAddress n:= ⟨0,univ,mem_univ _⟩
   intro h; specialize h V (mem_univ _); change 10 * pdist (V-0) < n.val at h; rw [sub_zero] at h
   have he: lift V=U:= lift_eq_iff.mpr ⟨rfl,fun i=>by
     unfold U a; rw [Pi.smul_apply,step_apply]; have ht:2*k≤n.val:=by unfold k; omega
     split; · simp; omega
     simp⟩
   have hp:= component_le V 0; rw [he] at hp; simp [U,a,nsmul_eq_mul] at hp; unfold k at *; omega
private def candidates (B:ℕ)(n:Side)(l:ℕ) := ∃ X:RegularAddress n,Wound X ∧ coverNumber B X.support=l
private lemma candidates_on (hn:20<n.val): ∃ l,candidates B n l:= by obtain ⟨X,h⟩:=beyond hn; exact ⟨_,X,h,rfl⟩
def brake (B:ℕ)(n:Side) := if h:20<n.val then Nat.find (candidates_on (B:=B) h) else 0
lemma put (hn:20<n.val): ∃ X:RegularAddress n,Wound X ∧ coverNumber B X.support=brake B n:= by
   change candidates _ _ _; rw [brake,dif_pos hn]; exact Nat.find_spec (candidates_on hn)
lemma cut (hn:20<n.val){X:RegularAddress n}(h: Wound X) : brake B n≤ coverNumber B X.support:= by
   rw [brake,dif_pos hn]; exact Nat.find_min' (candidates_on hn) ⟨_,h,rfl⟩
lemma toll (hn:20<n.val)(B:ℕ) : n.val ≤ 10*(brake B n*(4*B+2)+2*B) := by
   obtain ⟨X,h,hp⟩ := put (B:=B) hn; unfold Wound Nonwrapping at h; push Not at h; obtain ⟨x,hx,h⟩:=h; rw [← hp]; exact h.trans (Nat.mul_le_mul_left _ (Corona.extent _ B hx X.anchor))
lemma nonwrap_iff (hn:20<n.val){X:RegularAddress n}: Wound X ↔ ¬ Nonwrapping (expand X) X.site:= by
   have h : Nonwrapping (halo 2 ({X.site}:Support n)) X.site:= fun x hx=> by
     obtain ⟨a,ha,h⟩:= halo_spec.mp hx; rw [mem_singleton.mp ha,separation_comm] at h; omega
   constructor
   · exact fun hp hh=> hp fun i hi=> hh _ (mem_union_left _ hi)
   exact fun hh hp=> hh fun i hi=> ((mem_union.mp hi).elim (hp i) (h i))
-- wind patch at zero with room for halo2. Allows Consecutive after cast.
lemma cope (hn:20<n.val) (hp:2≤P.B) : ∃ X:Support n, halo 2 ({0}:Support n) ⊆ X ∧ ¬ Nonwrapping X 0 ∧ coverNumber P.B X ≤ brake P.B n +81:= by
   obtain ⟨X,h,hb⟩:= put (B:=P.B) hn; let c:Seat n := (1,-X.site); let X': RegularAddress n:= ⟨0, c.spread X.support, mem_image.mpr ⟨_,X.anchor,by simp [c,affine]⟩⟩
   have he:¬Nonwrapping X'.support X'.site:= mt (fun hp=> ((spin_wrap (1:Signed) (-X.site) (o:=X.site)).1 (?_))) h -- inspect
   swap; · simpa [affine, X',c, Seat.spread] using hp
   refine ⟨expand X', subset_union_right, (nonwrap_iff hn).1 he,(Geo.enlarge P X' hp).trans_eq ?_⟩
   change coverNumber _ (c.spread X.support)+81=_; rw [Seat.visit_count,hb]
section book
variable (g:G.Simple)
set_option quotPrecheck false
local notation "m" => (n.val:ℝ)
local notation "κ" => (Wind.ray (G:=G) P axes01)
local notation "γ" => (P.threshold)
def airGap (P:BudgetPoint)(n:Side) := Real.exp (-(preExponent P * brake P.B n))
def roomPrice (n:Side) (a:ℝ) := 6*a*(n.val:ℝ)^10
def chunk (P:BudgetPoint) (n:Side) (a:ℝ):= roomPrice n a * airGap P n
lemma flatX (x y:Site n): (coord x y axes01.val.1)^2 ≤ m^2:= by
  unfold coord; let z:= lift (y-x) axes01.val.1; have h:=lift_centers (y-x) axes01.val.1
  have hx:z ≥ -(n.val:ℤ) := by unfold z; omega
  have hy:z ≤ (n.val:ℤ) := by unfold z; omega
  have hv: -(n.val:ℝ)≤z:=by exact_mod_cast hx
  have hu:(z:ℝ) ≤ m := by exact_mod_cast hy
  change (z:ℝ)^2 ≤ m^2; nlinarith
variable {A:RegularAddress n}(h:P.Regular A.support f)(ht:P.supBounds A.site A.support f b)
include h ht g
lemma rural (v:Dir G n)(hd:∀ o,P.dirBound o v) : |logHessian f v v| ≤ b := by
   rw [hessian_diag g h]; exact ht.2 1 (flat_ok P _) [v,v] (by have hx:=P.order_ge; simp; omega) (by simp [hd]) -- may rewrite anywhere
lemma plate_toll (x y:Site n) : γ^2 * |logHessian f (lamp axes01 x) (lamp axes01 y)| ≤ 6*b:= by
   have hu:= P.threshold_pos; have hp:=abs_le.mp (rural g h ht _ (core g P axes01 x)); have hr:= abs_le.mp (rural g h ht _ (core g P axes01 y)); have he:=abs_le.mp (rural g h ht _ (core' g P axes01 x y))
   rw [grant P axes01 x y, abs_mul,abs_of_nonneg (by positivity : 0≤((P.threshold/2)^2)⁻¹), ← mul_assoc, show γ^2*((γ/2)^2)⁻¹=(4:ℝ) by field_simp; norm_num, polar P _ _ _ h,abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
   cases abs_cases (logHessian f (κ x+κ y) (κ x+κ y)-logHessian f (κ x) (κ x)-logHessian f (κ y) (κ y)) <;> rename_i ha <;> rw [ha.1] <;> linarith [hp.1,hp.2,hr.1,hr.2,he.1,he.2] -- arithmetic cases
lemma planeFare : γ^2 * |Anchor.plane axes01 f| ≤ roomPrice n b:= by
  unfold Anchor.plane; let u (x y:Site n):= logHessian f (lamp axes01 x) (lamp axes01 y); let c(x y:Site n):= (coord x y axes01.val.1)^2; have hh (x y): 0≤ c x y:=sq_nonneg _
  have he : 0≤b:= ht.1; let S:=γ^2
  have hS:0≤S:= sq_nonneg _
  have ha(x:Site n):S * |∑ y, c x y*u x y|≤∑ _y:Site n,m^2 * (6*b):= by
    apply le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) hS); rw [mul_sum]; apply sum_le_sum; intro y _; rw [abs_mul,abs_of_nonneg (hh x y),mul_left_comm]; exact (mul_le_mul (flatX x y) (plate_toll g h ht x y) (mul_nonneg hS (abs_nonneg _)) (sq_nonneg _))
  rw [abs_mul,abs_of_nonpos (by norm_num : -(1/2:ℝ) ≤ 0)]; change S * (- - (1/2:ℝ)*|∑ x,∑ y,c x y*u x y|) ≤ _; rw [mul_left_comm]; have hp : |∑ x,∑ y,c x y*u x y| ≤ ∑ x,|∑ y,c x y*u x y|:= abs_sum_le_sum_abs ..
  have hv:= mul_le_mul_of_nonneg_left hp hS; rw [mul_sum] at hv
  have h':= hv.trans (sum_le_sum (fun i _=>ha i)); simp only [sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow] at h'; unfold roomPrice; exact (mul_le_of_le_one_left (mul_nonneg hS (abs_nonneg _)) (by norm_num : - -(1/2:ℝ) ≤ 1)).trans (h'.trans_eq (by ring))
end book
section mismatch
variable {S:Listing G n}{T:Collection.Source G n} (g:G.Simple)(hn:20<n.val)(hR:Collection.Local R P F a t) (hS:Collection.Local S P T b w)
local notation "γ" => (P.threshold)
local notation "Δ" => delta
local notation "A" => R.read F
local notation "V" => S.read T
local notation "K" => trove P axes01
local notation "H" => (Fintype.card (Site n):ℝ)
include hn hR g
lemma canonical : γ^2 * |K A-H* Δ A| ≤ H * chunk P n a:= by
  let h (i:ℕ):=plane axes01 (F.logRead i); let g'(i:ℕ):= projection (R.reg i) (F.logRead i) axes01 axes01
  obtain ⟨u,hu,hk⟩:= hR.cheap; let s:=h-g'; let t i:= γ^2* s i; have ht:0≤γ^2:=sq_nonneg _; let b i:=u i*Real.exp (preExponent P * coverNumber P.B (R.reg i).support)
  have he : Summable t:= (((sum_trove g P axes01 hR).summable.sub (hR.projects.series g axes01 axes01)).mul_left (γ^2))
  have hp: γ^2 * |K A - H*Δ A|=|∑' i,t i|:= by
    rw [Roof.Vale.Calibre.apportion g (by omega) _ P hR.projects hR.transforms, ←(sum_trove g P axes01 hR).tsum_eq,← (sum_trove g P axes01 hR).summable.tsum_sub (hR.projects.series g axes01 axes01), ← abs_of_nonneg ht,← abs_mul]; -- maybe rewrites in he
    unfold t s h g'; rw [tsum_mul_left]; rfl
  rw [hp]
  apply le_trans (norm_tsum_le_tsum_norm he.norm)
  have hK: SumBudget b (H*a):= by
    have h:= budget_over Finset.univ _ (fun _=>a) (fun x hx=> hk x); simpa only [sum_const,card_univ,nsmul_eq_mul, sum_ite_eq, Finset.mem_univ, if_true, b] using h
  let v:=6*(n.val:ℝ)^10*airGap P n; have hv : 0≤v:= by unfold v airGap; positivity
  have hr: SumBudget (fun i=> ‖t i‖) (H*chunk P n a) := by
    have hi (i): ‖t i‖ ≤ v * b i := by
       by_cases hA: Nonwrapping (expand (R.reg i)) (R.reg i).site
       · rw [show t i=0 from (by unfold t s h g'; rw [Pi.sub_apply,planar g (by omega) _ _ hA (hR.smooth i),sub_self,mul_zero]), norm_zero]; exact mul_nonneg hv (hK.1 i)
       simp only [Real.norm_eq_abs,t,s,h,g',abs_mul, Pi.sub_apply, projection, if_neg hA,sub_zero,abs_of_nonneg ht]
       have hh: airGap P n * Real.exp (preExponent P*coverNumber P.B (R.reg i).support) ≥ 1:= by
          have hp:= cut (B:=P.B) hn ((nonwrap_iff hn).2 hA)
          have he:(0:ℝ)≤preExponent P:=by unfold preExponent; linarith [P.exponent_pos]
          unfold airGap; rw [←Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (show (brake P.B n:ℝ)≤ (coverNumber P.B (R.reg i).support:ℝ) from (by exact_mod_cast hp)) he]
       refine (planeFare g (hR.smooth i) (hu i)).trans ((le_mul_of_one_le_right ?_ hh).trans_eq (?_))
       · unfold roomPrice; have ht:=(hu i).1; positivity
       unfold roomPrice v b; ring
    refine budget_loosen (budget_mono (budget_scale hv hK) (g:=fun i=>‖t i‖) (fun i=>norm_nonneg _) hi) ?_; unfold chunk roomPrice v; apply le_of_eq; ring
  exact hr.2.2
include hS
lemma accrue {r:ℝ}(hp:∀ W,Sunny P W → r + (A).additive P W=(V).additive P W) : γ^2 * |Δ A-Δ V| ≤ chunk P n a+chunk P n b:= by
   let v:= K A; have h:v=K V:=trove_fare P axes01 A V r hp
   have h1:= canonical g hn hR; have h2:= canonical g hn hS; let m:=γ^2; let s:=H
   have h₀:0<s:=by unfold s; positivity
   rw [← h] at h2
   change m * |v-s*Δ A| ≤ s*chunk P n a at h1
   apply le_of_mul_le_mul_left (a:=s) _ h₀
   calc
     s*(γ^2*_) = m*|(v-H*Δ V) - (v-H*Δ A)| := by rw [show (v-H*Δ V) - (v-H*Δ A)=s*(Δ A-Δ V) from (by unfold s; ring),abs_mul,abs_of_pos h₀]; unfold m; ring
     _ ≤ _ := by apply le_trans (mul_le_mul_of_nonneg_left (abs_sub ..) (sq_nonneg γ)); linarith only [h1, (show m*|v-s*Δ V| ≤  s* chunk P n b from h2)] -- linarith s reducible?
end mismatch
end YM.AnalyticBridge.VerifiedReset.Averaging.Wind
#print axioms YM.AnalyticBridge.VerifiedReset.Averaging.Wind.accrue

import YM.RemainderComparison.Lyric.Tactus

/-!
# Connected weighted residual on revealed semantic support addresses

The first book multiplier `l p i` need not be a power of the support; can
be 0, etc. Can reuse after buying tagged E or longer inherited analytic
payloads. Draw graph allocation slots separately using their actual positive
cash; supports inclusive masks and costs phthal. Includes vertex conjuncts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Foundations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ} {O:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(X:Coat T F)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)
variable (f':H.ThinP→Drums M S→ℝ) {N:Captain H j q d v u A b r B e n χ}
variable (z:H.fragrances) (r':ι→ℝ) (γ: H.ThinP→Drums M S→ℝ)

omit [Fintype ι] in
lemma fisc (p:Drums M S) (v:ι→ℝ) (u:Molecule S) (B:ℝ) (k:ℕ)
    (f : Head S→ℝ):
    (∏i∈p.val,v i) * (if p.reach⊆u then
       (B*(team M p).weight)*(∏ i∈u\p.reach,f i)*(1+H.shapeW u)^k else 0) =
    (if p.reach⊆u then (∏i∈p.val,wages M v i)*∏ i∈u\p.reach,f i else 0)*(B*(1+H.shapeW u)^k):=by
  split
  · rw [Palette.worth]; unfold Palette.wages; rw [prod_mul_distrib]; ring
  · rw [mul_zero,zero_mul]

def roof (u:H.ThinP) (j:ℕ) := (2:ℝ)^j*∑ i:Drums M S, (∏ s∈i.val,r' s)*γ u i*f' u i
def prim (w:Syllable M H z) (j:ℕ) := invests M H z w r'*adjectives M H z w f' j * ∏ i,γ (z.2 i) (w i)
def powerpoint (w:Syllable M H z) (j m:ℕ) := invests M H z w r'*dividend M H z w f' j m * ∏ i,γ (z.2 i) (w i)
lemma symphony (j:ℕ) : ∑ w:Syllable M H z,prim M H f' z r' γ w j=clusters H.seam (fun u=>roof M H f' r' γ u j) z.2:=by
   symm
   let F u w:=2^j*((∏ s∈(w:Drums M S).val,r' s)*γ (z.2 u) w*f' (z.2 u) w)
   have h: clusters H.seam (fun u=>roof M H f' r' γ u j) z.2= ‖cadence H z‖ * ∏ u,∑ w,F u w:=by
      unfold cadence clusters; rw [norm_div,Real.norm_eq_abs (coefficient ..),Real.norm_of_nonneg (by positivity:0≤ ((z.fst+1).factorial:ℝ))]; unfold F; simp_rw [← Finset.mul_sum]; unfold roof; ring
   rw [h,Fintype.prod_sum F,Finset.mul_sum]; refine sum_congr rfl fun w _=>?_; unfold prim adjectives invests F; simp_rw [prod_mul_distrib]; ring
variable {δ e₁ q':ℝ}
lemma gathers (hp:Paid M H χ N f') (hr:∀ i,0≤r' i) (hγ:∀ p i,0≤γ p i)
    (ha:0≤ a)(m:ℕ) (hq:Ready H.smallAt (radiusB x) (fun u=>roof M H f' r' γ u j) (a+δ) e₁ δ q') :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z:H.fragrances=>∑w:Syllable M H z,powerpoint M H f' z r' γ w j m) a
        (collars G δ x j m * (e₁ * (1-q')⁻¹)) := by
   intro x'; have ht:= log_hit_tail H.seam H.smallAt (radiusB x) H.testS hq (add_nonneg ha hq.2.1.le) 0 x'
   simp only [pow_zero,mul_one] at ht
   let S:= shiftG x; have he:0 ≤ S:=by unfold S shiftG; positivity
   let v:= collars G δ x j m; have hv:0 ≤ v:=by unfold v collars Reserves.polyPrice; have he := hq.2.1; positivity
   have hW := budget_scale hv ht
   refine budget_mono hW (fun z=> ?_) (fun z=>?_)
   · dsimp only; split
     next =>
       apply mul_nonneg _ (Real.exp_pos _).le; exact sum_nonneg fun i _=> mul_nonneg (mul_nonneg
         (prod_nonneg fun i _=> prod_nonneg fun j _=>hr j) (dividend_nonneg M H χ hp z i)) (prod_nonneg fun i _=> hγ _ _)
     exact le_rfl
   dsimp only; split; next h=>
     rw [if_pos (show 0 ≤ z.fst ∧ x'∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,h⟩), ← symphony M H f' z r' γ j,Finset.sum_mul,Finset.sum_mul,Finset.mul_sum]; refine sum_le_sum ?_
     intro w _; unfold powerpoint dividend prim; rw [mul_pow];
     let u:ℝ:= coverNumber (radiusB x) (reachability z)
     have hF := polynomial_cost hq.2.1 (show 0 ≤ u from Nat.cast_nonneg _) (m*j)
     let f:= invests M H z w r'; let l:=∏i,γ (z.2 i) (w i); let p:= adjectives M H z w f' j
     have hf:0≤f:=prod_nonneg fun i _=>prod_nonneg fun i _=>hr _
     have hl:0≤l:=prod_nonneg fun i _=> hγ _ _; have hs: 0≤p:=mul_nonneg (norm_nonneg _) (prod_nonneg fun i _=> mul_nonneg (by positivity) (hp.fare ..))
     change f*(S^(m*j)*(1+u)^(m*j)*p)*l*Real.exp (a*u) ≤ v*(f*p*l*Real.exp ((a+δ)*u))
     apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF (pow_nonneg he _)) hs) hf) hl) (Real.exp_pos _).le).trans_eq
     rw [add_mul, Real.exp_add]; unfold v collars S polyPrice; ring
   next => exact hW.1 z

def Bill (j:ℕ)(w:Syllable M H z) (s:ℕ):= invests M H z w r' * dividend M H z w f' j s

/-- Uniform earned veto. Can filter the SAME represented series by any `X`
meeting this quantitative retention. No claims that earthquake is false. -/
lemma run (hp:Paid M H χ N f')(hr:∀ i,0≤r' i)(hγ:∀ p i,0≤γ p i)
    (ha:0≤a)(m:ℕ) (hq:Ready H.smallAt (radiusB x) (fun u=>roof M H f' r' γ u j) (a+δ) e₁ δ q')
    (V: (z:H.fragrances)→Syllable M H z→Prop)(v:ℝ)(hv:0≤v)(hP: ∀ z w,V z w → 1≤ v*∏ i, γ (z.2 i) (w i)) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>∑ w:Syllable M H z, if V z w then Bill M H f' z r' j w m else 0) a
       (v*(collars G δ x j m * (e₁ * (1-q')⁻¹))) := by
   intro x'
   have ht := budget_scale hv (gathers M H χ f' r' γ hp hr hγ ha m hq x'); have hz z w:0≤Bill M H f' z r' j w m:=mul_nonneg
    (prod_nonneg fun i _=> prod_nonneg fun j _=>hr _) (dividend_nonneg M H χ hp z w)
   refine budget_mono ht (fun i=>?_) (fun i=>?_)
   · split
     · apply mul_nonneg _ (Real.exp_pos _).le; exact sum_nonneg fun i _=> by split; exact hz _ i; exact le_rfl
     exact le_rfl
   dsimp only; split
   next h=>
    rw [← mul_assoc,Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    refine sum_le_sum ?_; intro w _; by_cases he: V i w
    swap; · rw [if_neg he]; exact mul_nonneg hv (mul_nonneg (hz i w) (prod_nonneg fun j _=> hγ _ _))
    rw [if_pos he]; exact (le_mul_of_one_le_left (hz i w) (hP i w he)).trans_eq (by unfold Bill powerpoint; ring)
   rw [mul_zero]
end YM.RemainderComparison.Lyric

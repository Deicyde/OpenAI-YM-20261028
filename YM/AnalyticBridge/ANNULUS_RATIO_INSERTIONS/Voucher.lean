import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Flare

/-!
Keep the local exponent and multiplier conventions described above
(see `order`). DOES NOT bound the entire transformed multiplier (even
pointwise there are sign-indefinite z corrections and log scalars that
remain, see exact decomposition). Consumer can pick the pair-log diag
term of its choice here; no hiding error of replacing the entire
determinant this way. Cost measured per link at this port, quantitative
consumer for the window variant later. Local price in number of typed
seeds even **after dropping remote defaults**. With true q profile prereqs
(extended enough for the particular buys).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest Dress
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (O A : Stores S) (T : Tube G S) (x W : ℝ) (V : Config G c) (k : S.Choices) (q : Chi)
  (d : ℝ) (J : ChartRatio G) (p : Rep G f)

variable (F : Forest S.ratio)
abbrev Mean := LinkArray G (Frozen A x F) → Prices G (Active A x F)
abbrev GaussArgs := LinkArray G (Frozen A x F) × Prices G (Active A x F)

variable (Y : LinkArray G (Frozen A x F))
  (z : Prices G (Active A x F))
  (L : Bond f → ℝ) (m : Mean (G:=G) A x F)

/-- k fixed, also in m(Y), use meanLog and fog on the same k.
No cloud chosen inside a factor. -/
def mixed := m Y + coupling p.beta • z

def volumeRead := Next.SectorChange.physical A F V Y (tape (mixed A x p F Y z m))

/-- Parts of drows and adjustment which are compulsory by . -/
def feeRow (D : ℕ) :=
  let a := mixed A x p F Y z m
  let U := volumeRead A x V p F Y z m;
  -(p.beta) * averaged (debt T x V k (shots S x) A F q d Y O D U a) -
    averaged (fun s => extraction T x V k (shots S x) A F q d Y
      (hot (turnStore s O) D (radiusB x)) (m Y) s) / (coupling p.beta)^2

def packet (uniform : Bool) (b : Finset ℕ) (D R R' : ℕ) :=
  let a := mixed A x p F Y z m
  let U := volumeRead A x V p F Y z m
  due O A x W V k p U q uniform R b * rentals O A F x q d J a R' * shortfall O A F x J p.beta *
    Real.exp (feeRow O A T x V k q d p F Y z m D + insertLog O (D*radiusB x) L)

/-- Charge without assuming global realizability of the unretained
defaults. If `Issued` using global `Authorized`, wants actual V flag
equality as supplied at correct sectors (also used for choice of fog).
For purely local estimation can instead use only the indicated
`Issued` near these addresses. Frequencies, tree, active coordinates etc
exactly `dyed`'s; in particular applies to fog/meanLog (see commission).
Take O any isle, including union upper bound before doing exact pieces.

H = salary in LFR Ledger, sufficient if can pay rental and log/tag charged
here (can use any # seed arrangement where receipts fit this *per-link*
overhead). Return **unused** e' valuation on these same factors besides a
fixed portion of compulsory gain. No including K price, indicator drop,
activity error, chain tails or any other inputs, and no charging
rest of all-determinant (it remains, explicitly).
-/
theorem valued (uniform : Bool) (b : Finset ℕ) (l D R R' : ℕ)
    {P : Teller G} {κ K H E C B e' : ℝ} {N : Side}
    (hl : S.patch.L = N) (hh : 100*(1+radiusB x) ≤ c.val) (hT : P.Funds S T) (hw : 0<W)
    (hD : 2≤D) (hR : (D+5)*radiusB x ≤ R) (hR' : (D+1)*radiusB x ≤ R')
    (h1 : R+1≤l*radiusB x) (h2 : R'≤l*radiusB x) (h3 : D+5≤l)
    (hi : Isle O A l (radiusB x))
    (hA : Aperture P N W K x)
    (hd : d=K*fiery G x N) (ht : d≤1) (he : 0≤E)
    (hG : ∀ a : G.Color, ‖a‖ ≤ 4*d → |Real.log (J.J a)| ≤ E*‖a‖^2)
    (n : ℕ) (hn : 4≤n) (hL : Ledger P N W κ (2*K) H n D x) (hκ : PointCharge T x W κ)
    (hβ : p.beta∈Set.Icc (Scales.y G N x/2) (2*Scales.y G N x)) (hC : 0≤C)
    (hg : -Real.log (spare J p.beta) ≤ C*(1+Real.log (Scales.y G N x)))
    (hq : ∀ s, Issued x V k (shots S x) A F (hot (turnStore s O) D (radiusB x)) s)
    (hB : 0≤B) (hy : ∀ i∈qLogs O (D*radiusB x), L i ≤ B)
    (salary : AnnulusRatioInsertions.tally C E N l + (tagCurrency S.patch l + B*(vans N l:ℝ) + e') ≤ H) :
    Real.exp (coin G N e' n x * O.shares) *
      ‖packet O A T x W V k q d J p F Y z L m uniform b D R R'‖ ≤
      Real.exp (-κ/4*(Scales.p G N x)^2*O.shares) := by
  classical
  let a := mixed A x p F Y z m
  let U := volumeRead A x V p F Y z m
  let tag := due O A x W V k p U q uniform R b
  let rent := rentals O A F x q d J a R'
  let spend := shortfall O A F x J p.beta
  let fee := feeRow O A T x V k q d p F Y z m D
  let press := insertLog O (D*radiusB x) L
  let amt (s : ℝ) := coin G N s n x * O.shares
  let earned := Real.exp (-κ/4*(Scales.p G N x)^2*O.shares)
  change Real.exp (amt e')*‖tag*rent*spend*Real.exp (fee+press)‖ ≤ earned
  by_cases hh' : tag*rent=0
  · rw [hh']; simp only [zero_mul,norm_zero,mul_zero]; exact (Real.exp_pos _).le
  have hwide := due_prereq O A x W V k p U q uniform b (left_ne_zero_of_mul hh') hR hw (hl.symm ▸ hA.1)
    (funds_branch hT)
  have hdoor := rental_border O A F x q d J a R' (right_ne_zero_of_mul hh')
  have hpose := licensed A F x V Y q d a hR' hl hh hT hA hd (show D≤l by omega) (show 5≤l by omega) hi hwide hdoor
  let u := orientedLog x V (shots S x) A F q d Y a
  have hp := ApertureSpan hA hl hh hT
  have hv s := debited T x V k F q d hi hD hp hT s (hq s) a U (Y:=Y)
  have hh0 : SliceSet S F U := on_fixed A F x V Y a
  obtain ⟨h4,h5⟩ := used U V O (Harvest.crown x O D) (clipping x A F O D) k u F A hl hh hT p.beta (2*K) H W κ D n hκ hL hβ hh0 hpose
  have ha : 0 ≤ averaged (fun s => extraction T x V k (shots S x) A F q d Y
      (hot (turnStore s O) D (radiusB x)) (m Y) s) := by
    unfold averaged
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => extraction_pos ..)
  have hfee : Real.exp fee ≤ earned * Real.exp (-(amt H)) := by
    apply le_trans _ (h5.trans (le_of_eq ?_))
    · unfold fee feeRow Affine.vital
      change Real.exp (-p.beta * averaged (debt _ _ _ _ _ _ _ _ _ _ _ _ U a)-_) ≤ _
      have he : debt T x V k (shots S x) A F q d Y O D U a = credits U V O _ _ T x k u := funext hv
      rw [he]; exact Real.exp_monotone (sub_le_self _ (div_nonneg ha (sq_nonneg _)))
    unfold earned amt; rw [sub_eq_add_neg,Real.exp_add]
  let Λ := tagCurrency S.patch l
  let Ω := B*(vans N l:ℝ)
  have hΛ : 0≤Λ := nonneg_currency ..
  have hΩ : 0≤Ω := mul_nonneg hB (Nat.cast_nonneg _)
  have hx : D*radiusB x+1 ≤ l*radiusB x := (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega : D≤D+5)) _).trans
    ((Nat.add_le_add_right hR _).trans h1)
  have hshare s (hs : 0 ≤ s) : s*((radiusB x:ℝ)+1)^4*O.shares ≤ amt s := by
    unfold amt coin; rw [show ((radiusB x:ℝ)+1)=Scales.b x from add_comm ..]
    have ht : 0 ≤ Real.log (Scales.y G N x) := Real.log_nonneg hL.1.le
    have ho := pow_le_pow_right₀ (Scales.size x) hn
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply (mul_le_mul_of_nonneg_left ho hs).trans
    exact le_mul_of_one_le_right (mul_nonneg hs (by have := Scales.size x; positivity)) (by linarith)
  have ha0 : ‖tag‖ ≤ Real.exp (amt Λ) := (due_bound _ _ _ _ _ _ _ _ _ _ _ _ (funds_branch hT)).trans
    ((conv_bound O uniform R l (radiusB x) h1).trans (Real.exp_monotone (hshare Λ hΛ)))
  have hpr := log_price O _ _ _ hx L hB hy
  rw [hl] at hpr
  have ha1 : press ≤ amt Ω := hpr.trans (hshare Ω hΩ)
  have hx : 1≤radiusB x := le_trans (by decide) hA.2.2.2.1
  rw [← hl] at salary hg hL hd
  have h0 : 0<d := by rw [hd,hl]; exact hA.2.1
  have hkt := local_salary O A F x q d J a R' l h2 n hn hx h0 ht hG he hC (G:=G) hL.1.le (β:=p.beta) hg salary
  rw [hl] at hkt
  change Real.exp (amt (Λ+Ω+e')) * (spend * ‖rent‖) ≤ Real.exp (amt H) at hkt
  rw [norm_mul,norm_mul,norm_mul,Real.norm_of_nonneg (show 0≤spend from (Real.exp_pos _).le),Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_add]
  have hearn := (Real.exp_pos (-κ/4*(Scales.p G N x)^2*↑O.shares)).le
  calc
    _ ≤ Real.exp (amt e') * (Real.exp (amt Λ)*‖rent‖*spend*(earned*Real.exp (-(amt H))*Real.exp (amt Ω))) := by
      have hx : 0≤spend := (Real.exp_pos _).le; gcongr
    _ = Real.exp (amt (Λ+Ω+e'))*(spend*‖rent‖)*(earned*Real.exp (-(amt H))) := by
      rw [show amt (Λ+Ω+e')=amt Λ+amt Ω+amt e' by unfold amt coin; ring,Real.exp_add,Real.exp_add]
      ring
    _ ≤ Real.exp (amt H)*(earned*Real.exp (-(amt H))) := by gcongr
    _ = _ := by rw [Real.exp_neg]; field_simp
where
  ApertureSpan (hA : Aperture P N W K x) (hm : S.patch.L=N) (hx : 100*(1+radiusB x)≤c.val) (hh : P.Funds S T) :=
    (hA.2.2.2.2 _ _ S T hm hx hh).1

end YM.AnalyticBridge.AnnulusRatioInsertions

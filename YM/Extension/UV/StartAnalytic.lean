import YM.Planned.RECIPE_STARTUP_PORT.Layout

/-! Analytic coupling of the canonical startup pot and kettle. Conditioned here on the TOP
recipe actually using these same payloads, and on the stock loan at both band endpoints. Fields U
stay real. We do not move a flag, and use *complete* fused forced occurrences (even winding ones).
No conclusions about group-coordinate analyticity or approximating a Haar integral by a Gaussian.
This is the fine boundary, not the complex nonlinear step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Startup
open Set Filter Function Lattice Wilson RG RG.Supply Precision Input Tree Ovens Ovens.Pipes
open WilsonStartup Progress.DirectedRecipe Progress.DirectedRecipe.Rack Planned
open scoped Topology BigOperators Classical Start
variable {G:Gauge} {n:Side}

/-- Complex functions evaluated on real link configurations. -/
def forcedLetter (c:Clip) (b:BudgetPoint) (z:ℂ) (i:ℕ) (U:Config G n) : ℂ :=
  if Padded.fixed (Start.Foot n) i ∧ Start.admission b (Padded.name (Start.Foot n) i) U then
    Complex.exp (- z * charge c b (Padded.name (Start.Foot n) i).val.2 U) else 0
-- use the linear real payload at scale 1 and multiply; no choices in z
lemma forced_agrees (c:Clip) (b:BudgetPoint) (x:ℝ) (i:ℕ) (U:Config G n) :
    forcedLetter c b (x:ℂ) i U=((Start.payload c b G n x).forced i U:ℂ):=by
  unfold forcedLetter Start.payload Start.paid
  by_cases he : Start.admission b (Padded.name (Start.Foot n) i) U
  · simp only [ite_and,he,ite_true]
    split_ifs <;> norm_cast
    exact (if_pos he).symm
  have hd : ¬(Padded.fixed (Start.Foot n) i ∧ Start.admission b (Padded.name (Start.Foot n) i) U):= fun hz=>he hz.2
  rw [if_neg hd]
  dsimp only
  split_ifs
  · exact (congr_arg Complex.ofReal (if_neg he)).symm
  rfl

lemma forced_norm {c:Clip} {b:BudgetPoint} (hc:Decent c b) (i:ℕ) (U:Config G n) (z:ℂ) (x:ℝ) (hx: x≤z.re) :
     ‖forcedLetter c b z i U‖ ≤ |(Start.payload c b G n x).forced i U|:=by
  rw [← Real.norm_eq_abs, ← Complex.norm_real (r:=(Start.payload c b G n x).forced i U),← forced_agrees]
  unfold forcedLetter
  split_ifs with he
  · have ht := charge_price c b hc U (Padded.name (Start.Foot n) i).val.2
    have hs : 0≤charge c b (Padded.name (Start.Foot n) i).val.2 U:=by
      apply le_trans _ (ht _)
      · have hh:= gain_pos b; positivity
      rw [← he.2.2]; exact Finset.inter_subset_right
    simp only [Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero, Real.exp_le_exp]
    nlinarith
  rfl

local notation "pott" a:arg m:arg l:arg => Port.pot a m l
local notation "kett" a:arg m:arg l:arg x:arg => Port.kettle a m l x

/-- Full startup rep as actually seen at the kickoff by the shelf permutation and final merge,
parametric in the predetermined top Kin (uses only k.path N N). -/
def canonical {a:Levels G} {H:Horizon a} {O:ChartRatio G} (k:Kin H O) (N p:ℕ) (x:ℝ) := fromTop k N p x (pott a N p) (kett a N p x)

/-- Matching complex atoms *after* the merge, using the exact same supports from canonical.
This section proves entire component functions before a completion in any norm. -/
def embodiedK (a:Levels G) (N p:ℕ) (z:ℂ) (i:ℕ) (U:Config G (a.S.side N p)) : ℂ :=
   let c:=(a.params N).clip; let b:=a.budget N
   let X:=pott a N p
   let F:=folio G (a.S.side N p)
   if (addr F b i).eligible b.threshold U then ∏ j∈(F i).val, j.elim (fun m=> stuff (upK X) (forcedLetter c b z (n:=a.S.side N p)) m U) (fun _=>0) else 0

def embodiedE (a:Levels G) (N p:ℕ) (z:ℂ) (i:ℕ) (U:Config G (a.S.side N p)) : ℂ := z * (((widen (pott a N p) (kett a N p 1)).regular i U):ℂ)

section agreements
variable {a:Levels G}{H:Horizon a} {O:ChartRatio G} (k:Kin H O) (N p:ℕ) (x:ℝ) (t:ℂ) (i:ℕ) (U:Config G (a.S.side N p))
lemma E_function_real : embodiedE a N p (x:ℂ) i U=(canonical k N p x).activities.E i U:=by
   unfold canonical fromTop finish Ovens.Pipes.fused embodiedE widen
   dsimp only
   by_cases he : i∈range (upE (pott a N p))
   · obtain ⟨j,rfl⟩:=he; rw [stuffed,stuffed]; dsimp [Port.kettle,Start.payload]; split
     · obtain v | w:= (Padded.name (Start.Sheet (a.S.side N p)) j) <;> dsimp only [Start.written,Sum.elim_inl, Sum.elim_inr,Pi.smul_apply,smul_eq_mul]; unfold Start.weight; push_cast; ring
       simp
     simp
   simp [blank _ _ he]

lemma K_entire_piece : Differentiable ℂ (fun z=>embodiedK a N p z i U) := by
 unfold embodiedK
 dsimp only
 split_ifs with he
 · apply Differentiable.fun_finsetProd
   intro j hj
   cases j with
   | inl j=>
     simp only [Sum.elim_inl]
     set f:=upK (pott a N p)
     by_cases hv : j∈range f
     · obtain ⟨j,rfl⟩:=hv; simp only [stuffed]; unfold forcedLetter; split_ifs
       · fun_prop
       fun_prop
     simp only [blank _ _ hv,Pi.zero_apply]; fun_prop
   | inr => simp only [Sum.elim_inr]; fun_prop
 fun_prop

lemma K_function_real : embodiedK a N p (x:ℂ) i U=(canonical k N p x).activities.K i U:=by
   have hl : (widen (pott a N p) (kett a N p x)).logarithm = 0 := by
     funext j U; dsimp only [widen]; by_cases he:j∈range (upS (pott a N p))
     · obtain ⟨j,rfl⟩:=he; rw [stuffed]; rfl
     exact congr_fun (blank _ _ he) _
   have hcast (c b) : (forcedLetter c b x (n:=a.S.side N p) (G:=G)) = (fun i V=>((Start.payload c b G (a.S.side N p) x).forced i V:ℂ)):= funext fun i=> funext fun V=> forced_agrees ..
   unfold canonical fromTop finish Ovens.Pipes.fused embodiedK solid
   dsimp only
   split_ifs
   · push_cast
     refine Finset.prod_congr rfl fun j hj=> ?_
     cases j with
     | inl j =>
       simp only [Sum.elim_inl]
       change _ = ((stuff (upK (pott a N p)) (@Tap.forced G (a.S.side N p) (kett a N p x)) _ U):ℂ)
       by_cases he : j∈range (upK (pott a N p))
       · obtain ⟨j,rfl⟩:=he; rw [stuffed,stuffed,hcast]; rfl
       simp only [blank _ _ he,Pi.zero_apply,Complex.ofReal_zero]
     | inr j =>
       change 0=((((Real.exp ((widen (pott a N p) (kett a N p x)).logarithm j U)-1):ℝ)):ℂ); rw [hl]; simp
   exact Complex.ofReal_zero.symm
lemma K_norm_compare (hc:WilsonStartup.Decent (a.params N).clip (a.budget N)) (hx:x≤t.re) : ‖embodiedK a N p t i U‖ ≤ |(canonical k N p x).activities.K i U| := by
 rw [← Real.norm_eq_abs, ← Complex.norm_real (r:=(canonical k N p x).activities.K i U), ← K_function_real k]
 unfold embodiedK; dsimp only
 split_ifs
 swap; rfl
 rw [norm_prod,norm_prod]
 refine Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun j hj=>?_
 cases j with
 | inl j =>
   simp only [Sum.elim_inl]
   by_cases he : j∈range (upK (pott a N p))
   · obtain ⟨j,rfl⟩:=he; rw [stuffed,stuffed,forced_agrees, Complex.norm_real]
     exact forced_norm hc j U _ _ hx
   simp only [blank _ _ he,Pi.zero_apply,le_refl]
 | inr j => exact le_rfl
end agreements

section estimates
variable {a:Levels G}{H:Horizon a} {O:ChartRatio G} (k:Kin H O) (N p:ℕ)

lemma k_addresses (x y : ℝ) i: ((canonical k N p x).activities.forced i).support=((canonical k N p y).activities.forced i).support := rfl

lemma E_diff_real (x y B:ℝ) (hB:B ≠ 0) (i : ℕ):
   (canonical k N p x).activities.E i - (canonical k N p y).activities.E i = ((x-y)/B) • ((canonical k N p B).activities.E i) := by
  let z:= (canonical k N p 1).activities.E i
  have ht x : (canonical k N p x).activities.E i=x • z:= by
    funext U; have h:= E_function_real k N p x i U
    change (x:ℂ) * (z U)=_ at h; exact Complex.ofReal_injective ((Complex.ofReal_mul ..).trans h).symm
  rw [ht x,ht y,ht B,← sub_smul,smul_smul,div_mul_cancel₀ _ hB]
variable (hk: Port.AtTop k) (he:Start.Allows a N)
include hk he
lemma genuine_valid (x:ℝ) (h:x∈RG.Shoot.band a N) : (canonical k N p x).activities.Valid (a.budget N) (a.clock.allowance N) (a.clock.forcedAllowance N) := ((Port.card (p:=p) he (permissions a) hk).law x h).ingredients.gates ..
lemma genuine_eq (x : ℝ) (h:x∈RG.Shoot.band a N) : (canonical k N p x).eval=Wilson.bare x := by
   funext U
   have hy:= (Port.card (p:=p) he (permissions a) hk).law x h
   change (finish (k.path N N) (a.params N).clip (a.budget N) (pott a N p) (kett a N p x) x 0).eval U=_
   exact (hy.ingredients.unshifted ..).trans (hy.matches_raw U)

end estimates
end YM.Extension.UV.Startup

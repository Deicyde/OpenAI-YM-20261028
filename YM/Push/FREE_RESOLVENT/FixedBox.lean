import YM.Push.FREE_RESOLVENT.AlignProbe
import YM.Push.FREE_RESOLVENT.Vertical



/-!
# Post-L budgets for the finite boxes in the nonlinear affine coefficients

Uniform in period & cut. Use in derivative norm at any finite order given
color/component as an entry with the corresponding address in that actual
patch. Use Branches etc EXACTLY as specified, no Π-norm of an array of
ℛ-dependent dimension with no pricing.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine.View
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.F08 Lifted Mark
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c f' c' n : Side} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {h : f.val=c.val*P.L.val} {h' : f'.val=c'.val*P.L.val}

section compare
-- supply sufficient perturbation functions for cross geometry (use curves or many axes).
variable {X : Type*} [TopologicalSpace X] {x : X}
variable {p : X → pair G c f} {p' : X → pair G c' f'} {R : ℕ} {o : Site c} {o' : Site c'}
lemma fixedPred (hb : P.Branches K G) (t : (data h K).Choices) (t' : (data h' K).Choices) (s : Signed)
    (hc : 1<c.val) (hc' : 1<c'.val) (hy : Tendsto p (𝓝 x) (𝓝 0)) (hy' : Tendsto p' (𝓝 x) (𝓝 0))
    (H : ∀ᶠ u in 𝓝 x, Reads (p u) (p' u) h h' K o o' R)
    (z : Cover) (w : PAC G 1) (hx : size z+View.reach P+2 ≤ R) :
    (fun u => gaugeQ (data h K) s t (p u) (coarseHere s o z w)) =ᶠ[𝓝 x]
    fun u => gaugeQ (data h' K) s t' (p' u) (coarseHere s o' z w) := by
  have hz : Tendsto (fun u => ((p u).1, (0:Vec G f 1))) (𝓝 x) (𝓝 0) := ((continuous_fst.tendsto _).comp hy).prodMk_nhds tendsto_const_nhds
  have hz' : Tendsto (fun u => ((p' u).1, (0:Vec G f' 1))) (𝓝 x) (𝓝 0) := ((continuous_fst.tendsto _).comp hy').prodMk_nhds tendsto_const_nhds
  have hp := watches (data h K) t hb
  have hq := watches (data h' K) t' hb
  filter_upwards [H,hy.eventually hp, hy'.eventually hq, hz.eventually hp, hz'.eventually hq] with a ha h1 h2 h3 h4
  exact responseView hc hc' s z w hb ha hx h1 h2 h3 h4
end compare

-- stencil
lemma tile_root (S : StepData c f) (s : Signed) (i : tile G f) :
    ∃ w, i=fineHere S s (named S s i) 0 w := by
  let R := StepData.sendSites s (0:Site f)
  let y := R i.1
  refine ⟨(S.ratio.residue y, i.2), Prod.ext ?_ rfl⟩
  change i.1=R.symm _
  apply R.injective; rw [Equiv.apply_symm_apply]; unfold named bottom addr; rw [map_zero,add_zero]
  exact (S.ratio.unpack_at y).symm

lemma ring_root (s : Signed) (i : raw G c) : i=coarseHere s (namedCo s i) 0 i.2 := by
  refine Prod.ext ?_ rfl; let R := StepData.sendSites s (0:Site c)
  change i.1 = R.symm _
  unfold addr; rw [map_zero, add_zero]; exact (R.symm_apply_apply _).symm

lemma monotile (S : StepData c f) (s : Signed) (i : tile G f) (hc : 1 < c.val) :
    (fun x => faces S s (stopAt S (named S s i) 4 x) i) = fun x => faces S s x i := by
  ext x; obtain ⟨w,hw⟩ := tile_root S s i
  have he := (sees_here S (named S s i) 4 x).plaquettes hc hc s 0 w (by simp [size])
  change faces S s x _ = faces S s _ _ at he
  -- grid location rewrite on i
  apply Eq.symm
  convert he using 2

lemma monopole (S : StepData c f) (s : Signed) (i : raw G c) (t : S.Choices) (hc : 1<c.val)
    (hb : S.patch.Branches S.kernel G) :
    (fun x => gaugeQ S s t (stopAt S (namedCo s i) (View.reach S.patch+2) x) i) =ᶠ[𝓝 0]
      fun x => gaugeQ S s t x i := by
  let L := stopAt (G:=G) S (namedCo s i) (View.reach S.patch+2)
  have hh : Tendsto L (𝓝 0) (𝓝 0) := by simpa using L.continuous.tendsto 0
  have h : (fun x => gaugeQ S s t x (coarseHere s (namedCo s i) 0 i.2)) =ᶠ[𝓝 0]
      fun x => gaugeQ S s t (L x) (coarseHere s (namedCo s i) 0 i.2) := fixedPred (p:=id) hb t t s hc hc
        tendsto_id hh (Eventually.of_forall fun x => sees_here S (namedCo s i) (View.reach S.patch+2) x) 0 i.2 (by simp [size])
  rw [← ring_root s i] at h
  exact h.symm

-- Price at zero by restricting input to maps of norm ≤1 into one fixed finite torus
def area (R : ℕ) : Side := ⟨2*R+2,Nat.zero_lt_succ _⟩

private lemma room_gt_one (R : ℕ) : 1 < (area R).val := by change _ < 2*R+2; omega
private lemma room_size (R : ℕ) : 2*R < (area R).val := by change _ < 2*R+2; omega

def refStep (P : Patch) (K : KernelChoices) (R : ℕ) :=
  Lifted.data (f:=area R * P.L) (c:=area R) (P:=P) rfl K

-- pull via all slots (including repeats). origin on target is 0.
variable (R : ℕ) (o : Site c)

def sheet (G : Gauge) (R : ℕ) (h : f.val=c.val*P.L.val) (K : KernelChoices) (o : Site c) :
    pair G c f →L[ℝ] pair G (area R) (area R * P.L) := by
  let X := area R; let M := refStep P K R
  let i := fun x : raw G X => coarseAt (G:=G) (r:=1) o (lift x.1) x.2
  let j := fun x : raw G (X * P.L) => fineAt (G:=G) (r:=1) (data h K) o (lift (M.ratio.parent x.1)) (M.ratio.residue x.1,x.2)
  exact (((LinearMap.funLeft ℝ ℝ i).toContinuousLinearMap.prodMap
    ((LinearMap.funLeft ℝ ℝ j).toContinuousLinearMap)))

lemma transported (p : pair G c f) : Reads p ((sheet G R h K o) p) h (show (area R * P.L).val=_ from rfl) K o 0 R := by
  constructor
  · intro z hz i
    change _ = p.1 (coarseAt (G:=G) (r:=1) o (lift (addr (0: Site (area R)) z)) i)
    rw [addr,zero_add,size_centers _ _ hz (room_size R)]
  intro z hz i
  let y := fineAt (G:=G) (r:=1) (refStep P K R) 0 z i
  let q := (refStep P K R).ratio
  change _=p.2 (fineAt (G:=G) (r:=1) (data h K) o (lift (q.parent y.1)) (q.residue y.1, y.2))
  erw [show q.parent y.1=addr 0 z from bottom_pp .., show q.residue y.1=i.1 from bottom_pr ..,addr,zero_add,size_centers _ _ hz (room_size R)]; rfl

lemma transported_size : ‖sheet G R h K o‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p; rw [one_mul,Prod.norm_def]; refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
    let i := coarseAt (G:=G) (r:=1) o (lift j.1) j.2
    exact (norm_le_pi_norm p.1 i).trans (norm_fst_le _)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  let M := refStep P K R
  let i := fineAt (G:=G) (r:=1) (data h K) o (lift (M.ratio.parent j.1)) (M.ratio.residue j.1,j.2)
  exact (norm_le_pi_norm p.2 i).trans (norm_snd_le _)

variable {R}
-- generic sup over fixed stage. Keep size symbolic. Include all occurrences from orders even if they share basis label.
-- separate
section bulk
variable {σ d A : ℝ} {v : ℕ}
-- Price once for D entries. h smooth used only in entry (global); price constants no h.
def faceBill (G : Gauge) (P : Patch) (K : KernelChoices) (v : ℕ) :=
  ∑ s : Signed, ∑ j : tile G (area 4 * P.L), ∑ i : Fin (v+1),
     ‖iteratedFDeriv ℝ (i.val+1) (fun u => faces (refStep P K 4) s u j) 0‖

def ductBill (G : Gauge) (P : Patch) (K : KernelChoices) (v : ℕ) :=
  let R := View.reach P+2; let t := Classical.arbitrary (refStep P K R).Choices
  ∑ s : Signed, ∑ j : raw G (area R), ∑ i : Fin (v+1),
     ‖iteratedFDeriv ℝ (i.val+1) (fun u => gaugeQ (refStep P K R) s t u j) 0‖

lemma bills_nonneg (G : Gauge) (P : Patch) (K : KernelChoices) (v : ℕ) :
    0 ≤ faceBill G P K v ∧ 0 ≤ ductBill G P K v := by
  constructor <;> (dsimp only [faceBill,ductBill]; positivity)

lemma receipts {α β X Y : Type*} [Fintype α] [Fintype β]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : α → X → β → ℝ) (a : α) (b : β) {f : Y → ℝ} (l k : ℕ) (hl : l ≤ k)
    (L : Y →L[ℝ] X) (hp : ‖L‖ ≤ 1) (hs : ContDiffAt ℝ ω (F a) 0)
    (he : f =ᶠ[𝓝 0] (fun y => F a (L y) b)) :
    ‖iteratedFDeriv ℝ (l+1) f 0‖ ≤ ∑ a, ∑ b, ∑ i : Fin (k+1), ‖iteratedFDeriv ℝ (i.val+1) (fun y => F a y b) 0‖ := by
  have h := (contDiffAt_pi.mp hs) b
  rw [(he.iteratedFDeriv ℝ _).eq_of_nhds]
  let g := fun x : X => F a x b
  change ‖iteratedFDeriv ℝ _ (g ∘ L) 0‖ ≤ _
  rw [Next.Foundations.jets_linear L (h.of_le le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ (l+1) g 0‖ * ∏ _ : Fin (l+1), ‖L‖ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..
    _ ≤ ‖iteratedFDeriv ℝ (l+1) g 0‖ := mul_le_of_le_one_right (norm_nonneg _) ((Finset.prod_le_prod
      (g:=fun _ => (1:ℝ)) (fun i _ => norm_nonneg _) (fun _ _ => hp)).trans_eq (by simp))
    _ ≤ _ := by
      let Z (a b) (i : Fin (k+1)) := ‖iteratedFDeriv ℝ (i.val+1) (fun x => F a x b) 0‖
      exact (Finset.single_le_sum (f:=Z a b) (fun i _ => norm_nonneg _) (Finset.mem_univ ⟨l,Nat.lt_succ_of_le hl⟩)).trans <|
        (Finset.single_le_sum (f:=fun i => ∑ j, Z a i j) (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _)) (Finset.mem_univ b)).trans <|
          Finset.single_le_sum (f:=fun a => ∑ i, ∑ j, Z a i j) (fun a _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)) (Finset.mem_univ a)

lemma face_tariff (S : StepData c f) (s : Signed) (i : tile G f) (hc : 1<c.val) {K : ℕ} (l : ℕ) (hl : l ≤ K) :
    ‖iteratedFDeriv ℝ (l+1) (fun z => faces S s z i) 0‖ ≤ faceBill G S.patch S.kernel K := by
  let o := named S s i
  obtain ⟨w,hw⟩ := tile_root S s i
  let W := refStep S.patch S.kernel 4
  apply receipts (fun s => faces W s (G:=G)) s (fineHere W s 0 0 w) _ _ hl
    (sheet G 4 S.sizes S.kernel o) (transported_size ..) (face_smooth _).contDiffAt
  refine Eventually.of_forall fun z => ?_
  exact Eq.trans (congrArg _ hw) ((transported 4 o z (G:=G) (h:=S.sizes)).plaquettes hc (room_gt_one _) s 0 w (by simp [size]))

lemma duct_tariff (S : StepData c f) (s : Signed) (k : S.Choices) (i : raw G c) (hc : 1<c.val)
    (hb : S.patch.Branches S.kernel G) {K : ℕ} (l : ℕ) (hl : l ≤ K) :
    ‖iteratedFDeriv ℝ (l+1) (fun z => gaugeQ S s k z i) 0‖ ≤ ductBill G S.patch S.kernel K := by
  let R := View.reach S.patch+2; let W := refStep S.patch S.kernel R
  let q := Classical.arbitrary W.Choices
  let y := namedCo s i
  let L := sheet G R S.sizes S.kernel y
  apply receipts (fun s => gaugeQ W s q (G:=G)) s (coarseHere s (0:Site (area R)) 0 i.2) _ _ hl
    L (transported_size ..) (duct_smooth hb _ q (S:=W))
  have he := fixedPred (p:=id) (x:=(0:pair G c f)) (p':=(L:pair G c f→_)) hb k q s hc (room_gt_one R) tendsto_id (by simpa using L.continuous.tendsto 0)
    (Eventually.of_forall (fun z => transported R y z (h:=S.sizes))) 0 i.2 (by unfold R; simp [size])
  exact EventuallyEq.trans (g:=fun x => gaugeQ S s k x (coarseHere s y 0 i.2)) (Eventually.of_forall fun x => congrArg (gaugeQ S s k x) (ring_root s i)) he
end bulk
end YM.FreeResolvent.Affine.View

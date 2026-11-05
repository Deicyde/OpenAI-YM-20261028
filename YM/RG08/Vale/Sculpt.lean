import YM.RG08.Vale.Basket
/-!
# S section already has polynomial zeros BELOW own weight at every issued rank
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {p m c f L:Side}{R S:ℝ}{D d e j r n i k t:ℕ}{F:Labels.Frame G d}{T:SectionData F}
variable (b: Letter F) (h:d ≤ D)(hv:1/2≤R)
private def windI (f:Potential G) (p:Side): Link G p:= fun i=> deckP f (lift i.1,i.2)
lemma sport {f:Potential G} (a:Finset Cover) : ∀ᶠ i:ℕ in atTop, salon a G (0:Site (boards i)) (windI f (boards i))=Place.ping a f := by
  filter_upwards [eventually_all.mpr (fun i:Spot a=> Next.Free.eventually_unfold boards board_end (Place.first i).val)] with i hi
  ext1 p; ext1 k
  change arm G (boards i) 1 (windI f (boards i)) (wrap (boards i) (Place.first p).val+_,Exterior.coord (Place.beam p)) k=_
  rw [add_zero,arm_apply]; unfold windI deckP heap; dsimp only; simp only [hi p,← coord_map, axisEquiv.symm_apply_apply]; rfl
set_option maxHeartbeats 600000 in
lemma crown_read (A:SectionData F)(x:Fin r→ Potential G)(a:Fin r→ℕ)(hp:∀ i,x i∈rangeLt _ (a i)) :
    wallet (crownP A b r) (fun i=>deckP (x i))= Tensor.coeff (pillar A b) r 0 (fun i=>ping A.stencil (x i)) := by
  let n:=∑ i,a i
  choose C hC He using fun i : Fin r=> v_purse (Place.grows _ (single_le_sum (fun j _=>Nat.zero_le (a j)) (mem_univ i)) (hp i): x i ∈ rangeLt _ n)
  let V:= Tensor.coeff (pillar A b) r 0; let w (k:ℕ) i:=windI (x i) (boards k)
  have hk:= stock_lank A.stencil V
  have Hf : ∀ (j:Fin r)(p:Fare G), Tendsto (fun i=> w i j (wrap (boards i) p.1,p.2)) atTop (𝓝 (deckP (x j) p)) := by
    rintro j p; apply EventuallyEq.tendsto
    filter_upwards [Next.Free.eventually_unfold boards board_end p.1] with i hi; unfold w windI; dsimp only; rw [hi]
  have he (i v z m) : ‖w m i (wrap (boards m) v,z)‖ ≤ C i*dime n v:= (He i (lift (wrap (boards m) v),z)).trans (mul_le_mul_of_nonneg_left (coins_wrap v n (boards m)) (hC i))
  have hm:=wallet_limit (H:=crownP A b r) (v:=w) board_end hk Hf n (fun i=>hC i) he
  apply tendsto_nhds_unique_of_eventuallyEq hm tendsto_const_nhds
  filter_upwards [eventually_all.mpr fun i=> sport (f:=x i) A.stencil] with k hk
  let S:=(0:Site (boards k))
  have hp : stitch (crownP A b r) (boards k) S=V.compContinuousLinearMap (fun _=> salon A.stencil G S):= by
    rw [crown_pays,back_sl]; unfold Tensor.coeff; rw [Next.Foundations.jets_linear (salon A.stencil G S) (show ContDiffAt ℝ r (pillar A b) 0 from ((Complex.reCLM.contDiff.comp (column_smooth ..)).contDiffAt.of_le le_top))]; rfl
  change stitch (crownP A b r) (boards k) S (w k) = _; rw [hp]; change V (fun i=> salon A.stencil G S (w k i)) = _; exact congr_arg V (funext hk)
theorem panning (A:Hol G)(hp:T.Sound A) (h:d≤D)(hv:0≤R)(i t): Abates (startU T b h hv i t) (fee b) := by
  intro W a hw g H
  unfold pass; rw [echo_start]; split
  next hL =>
    rw [chant,pointed]; split
    next hb=>
      rw [one_smul,crown_read b T W a hw]
      let u:= Place.column T b.label; let P:= (fun i:Fin t=> ping T.stencil (W i)); let c:= Complex.reCLM
      have hk : ∑ i,a i < (F.grades b.label).1 := by unfold fee at H; rw [← hb] at H; omega
      change ((t.factorial:ℝ)⁻¹) • (iteratedFDeriv ℝ t (c ∘ u) 0 P)=0
      rw [c.iteratedFDeriv_comp_left (column_smooth T b.label|>.contDiffAt) le_top]; change ((t.factorial:ℝ)⁻¹) • c (iteratedFDeriv ℝ t u 0 P)=0; rw [show iteratedFDeriv ℝ t u 0 P=_ from Place.lower A T hp b.label a hk W hw, _root_.map_zero, smul_zero]
    next ht=> simp
  next hL=> simp
lemma projected (H:Hol G)(hx:T.Sound H)(hp:Bid.pop T)(h:d≤D)(hv:0≤R)(v:Letter F) (hb:slot v=slot b): invest H (startU T b h hv 0 (slot b)) v= if v=b then 1 else 0 := by
  let U:= startU T b h hv
  have he:= outfit T b H hx hp h hv v 0
  rw [auditT] at he
  rw [sum_eq_single_of_mem (slot b) (Finset.mem_range.mpr (hb.symm ▸ Nat.lt_succ_self _)),if_pos (show slot v≤0+slot b by omega),show 0+slot b-slot v=0 by omega] at he
  · simpa only [true_and] using he
  intro i hi ht; rw [if_neg (by have h:=Finset.mem_range.mp hi; omega)]
-- Leading mathematical matrix at the same slot diagonal. With stated EXACT price ratio.
def priceLit (K:Flight j n)(b: Letter F):ℝ:= (K.L.val:ℝ)^ (d-fee b)
def leadingV (H:Hol G)(T:SectionData F) (he:d≤D)(hv:1/2≤R)(K:Flight j n)(s:ℝ)(b v:Letter F) :=
    invest H (aboard d (painted G (Carrier.linesOf K s)) (startU T b he ((by norm_num : (0:ℝ)≤1/2).trans hv) 0 (slot b))) v
include h hv
theorem capitalT (H:Hol G)(hx:T.Sound H)(hp:Bid.pop T)(K:Flight j n)(hs:0<S)(he:4≤n)(hr:d≤j)(v:Letter F)(hl:slot b=slot v)(hT:fee v≤fee b):
    leadingV H T h hv K S b v=if v=b then priceLit K b else 0 := by
  unfold leadingV
  let hg:0≤R:=(by norm_num : (0:ℝ)≤1/2).trans hv
  have hh:= start_duty T b h hg hp H hx
  rw [payout H hv K hs he hr (start_lank T b h hg 0 (slot b)) (seat_made hh) (panning b H hx h hg 0 (slot b)) v hT hl.symm,projected b H hx hp h hg v hl.symm]
  split
  next ho=>
    subst v; rw [mul_one, height, inv_pow]
    unfold priceLit; field_simp; rw [← pow_add, Nat.add_sub_of_le (show fee b≤d from b.bill)]
  next ho=> simp
end YM.RG08.Vale

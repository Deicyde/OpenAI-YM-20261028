import YM.RG08.Pivot.Month
/-!
# Zero-order frame at ONE coupling step unmasked. All marked
communication of kernel coordinates (not lists of arbitrary names). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Reflect Finset Needle Source Source.Drops Labels Planned.PrimaryIntegral295
open scoped Topology BigOperators
variable {I E : Type} {L: Side} {G:Gauge} {R c:ℝ} {r d n D t j : ℕ} {F:Frame G d} {S:SectionData F} {V:ReadsU F D R} {H:Hol G} {M:Session (Letter F)}
lemma glint_eq (b:Letter F)(h:Genuine H V) {j : ℕ}{w: Train j} (hp:0<c)(hj:4≤j) :
    let P:= plaza G c w none; let U := hot M 0
    let A:= frisk P ((bureau V M b) 0) d r
    A= ∑ i:Letter F,U i b • frisk P ((V i) 0) d r := by
  intro P U A
  have he: bureau V M b 0= ∑ i: Letter F, (U i b) • ((V i) 0) := by
    ext1 j; unfold bureau edgeBook; simp_rw [Finset.sum_apply]; apply sum_congr rfl; intro i _
    unfold fund adapt; simp only [Finset.sum_apply,Nat.zero_add, Pi.smul_apply, sum_range_one,footing (le_refl 0),Nat.sub_zero]; rfl
  obtain ⟨_,_,B⟩:= portion G hp hj
  rw [show A= _ from (congr_arg (fun v:Spine (Voice D R) (Loc G 1) => frisk P v d r) he), wick_sums (B w).1 (fun i=> U i b • V i 0) univ (fun i _ j=>(h.rank i|>.hem 0 j).scale _)]
  exact sum_congr rfl fun i _=> by unfold frisk; simp_rw [wick_wt,Finset.smul_sum]; rfl
lemma flare_out (a b:Letter F)(h:Genuine H V)(hp:0<c)(hj:4 ≤ j)(w:Train j) :
    let P:= plaza G c w none
    hearth H P (bureau V M) a b=(hearth H P V * hot M 0) a b := by
  intro P
  change invest H _ a= _
  let g i:= V i 0; let f i:= frisk P (g i) d (slot a); let L i:=hot M 0 i b
  obtain ⟨_,_,B⟩:= portion G hp hj
  have hf i: Gold (f i):= gold_sum (fun j _=> golden_terraces hp hj (W:=g i) (fun j=> sober_vetted (h.rank i)) w _ j)
  have he i: Polished (f i):= polished_sum (fun j _=> pol_front (U:=g i) (B w).1 (h.paid i 0) j (slot a))
  rw [show frisk P ((bureau V M b) 0) d (slot a) = _ from glint_eq b h hp hj]
  rw [invest_sum H a univ (fun i _=>tot_weight (hf i).toToute (L i)) (fun i _=> polished_scale (he i) _),Matrix.mul_apply]
  exact sum_congr rfl fun i _=> by change invest H (L i • f i) a = _; rw [invest_sm H a (L i) (hf i).toToute (he i),mul_comm]; rfl

variable (X:Chain)(u:G.ColorIndex)(σ:ChartRatio G)(p:Hol G)(S:SectionData F)(he:d≤D)(hx:1/2≤R)
abbrev fires (X : Chain) (G : Gauge) (N i) := plaza G X.kernel.penalty (X.history N i) none
local notation "Φ" => stepboard X u σ p S he hx
local notation "ξ" => dice X u σ p S he hx
def oven (N i : ℕ) : Loft F:= hearth p (fires X G N i) (Φ N i)
variable (K:KPrices X.kernel)(hp:X.Wake G)(hσ : LocalRatio σ)(hS:S.Sound p)(hB:Bid.pop S)
include K hp hσ hS hB
lemma oven_yes (hn : n≤t)(ho:d≤ X.J n): IsUnit (oven X u σ p S he hx t n).det := by
  obtain ⟨_,_,B⟩:= portion G X.kernel.penalty_pos (X.adm n); exact (settled_hearth p (Needle.decks X u σ p S he hx K hp hσ hS hB t n hn ho) (B _|>.1)).1
-- Exact effective push with test parameters. Coordinates are in G_k not parent.
omit K hS hB in
include hx in
lemma lint_aware (A: BoardU D R G) (n h:ℕ)(hG: Marvel n A)(hF: Lank A){N i:ℕ}(hv:i<N) (r:ℕ):
    let P:=Needle.push (dance X u σ N i) n h A; let W:=painted G (X.A₀ N i)
    frisk (fires X G N i) (P 0) n r=aboard h W (frisk (fires X G N (i+1)) (A 0) n r) := by
  intro P W
  have ht:= fairground X u σ hp hσ hv
  let D:= dance X u σ N i; let B:= filop D.cv D.tree D.song none n h A
  rw [show P 0=B 0 from funext fun a=> by rw [show P=hill D.scale B from rfl,Tall.ridge _ ht.once]; simp]
  exact olog_masts σ u hx (hp i) (X.adm _) (X.packing u σ hp hσ hv|>.gets) hG (hF 0) (X.az_whole N i) (fun c f H=> X.canonical N i hv H)
lemma oven_steps (hv:n<t)(hw:d≤X.J n) :
    let U := oven X u σ p S he hx; let k:=hot (ξ t n) 0
    U t n*k=diagonalSl k * U t (n+1) := by
  intro O Z
  let K':=dance X u σ t n
  have hn : d ≤ X.J (n+1):= hw.trans (X.mono n)
  have hx':=dice_step X u σ p S he hx K hp hσ hS hB t n hv hn
  have hf := Needle.decks X u σ p S he hx K hp hσ hS hB t n hv.le hw
  have hF := Needle.decks X u σ p S he hx K hp hσ hS hB t (n+1) hv hn
  ext a b
  obtain ⟨_,_,hP⟩:= portion G X.kernel.penalty_pos (X.adm n)
  obtain ⟨_,_,hP'⟩:= portion G X.kernel.penalty_pos (X.adm (n+1))
  let w₀ := X.history t n; let w:=X.history t (n+1)
  let μ:= fires X G t (n+1); let M:=Φ t (n+1) b; let L: BoardU D R G:= uprise K' (Φ t (n+1)) b
  let g i:=frisk μ (M 0) d i
  let P':=X.flight t n; let A:=painted G (X.A₀ t n)
  have hz:=fairground X u σ hp hσ hv
  have hQ:= (heart hz hx hF.toBoards).rank b
  let W:= fires X G t n
  have hL : frisk W (L 0) d (slot a)=aboard d A (frisk μ (M 0) d (slot a)):= by
    rw [← show frisk W (L 0) (slot b) (slot a)=_ from wick_carry (fun i hi=> not_ne_iff.mp (mt (hQ.cap 0 i) (by omega))) (M:=W) (hP w₀|>.1) (slot_le b),
      ← show frisk μ (M 0) (slot b) (slot a)=_ from wick_carry (M:=μ) (fun i hi=> not_ne_iff.mp (mt ((hF.rank b).cap 0 i) (by omega))) (hP' w|>.1) (slot_le b)]
    exact lint_aware X u σ hx hp hσ M _ _ (hF.rank b) (hF.paid b) hv (slot a)
  have hg i: Gold (g i):= gold_sum fun w _=> golden_terraces X.kernel.penalty_pos (X.adm (n+1)) (W:=M 0) (fun j=>sober_vetted (hF.rank b)) _ _ w
  have hg' i: Polished (g i):= polished_sum fun v _=> pol_front (U:=M 0) (hP' w|>.1) (hF.paid b 0) v i
  obtain ⟨V,ht',hW⟩:= demandPrint X u σ K hp hσ t n hv
  have he' i (ht:slot i=slot a): leadingV p S he hx P' X.kernel.penalty i a=Z a i := (arch_turn p P' X.kernel.penalty V K' X.kernel.penalty_pos (X.adm _) hn hz hx hS hB he ht' hW hF i a ht).symm
  rw [← show hearth p W (bureau (Φ t n) (ξ t n)) a b=(O t n * Z) a b from flare_out _ _ hf X.kernel.penalty_pos (X.adm n) w₀,← hx'.2]; unfold hearth
  rw [Matrix.of_apply,hL]; change invest p (aboard d (painted G (Carrier.linesOf P' X.kernel.penalty)) (g (slot a))) a = _
  rw [projection_prime p P' X.kernel.penalty_pos (X.adm _) hn hx (hg _) (hg' _) a rfl hS hB he,
      Finset.sum_filter,Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro k _; unfold diagonalSl; rw [Matrix.of_apply]; split_ifs with hh ht
  · rw [he' k hh]; apply congr_arg (Z a k *·)
    change invest p (g _) k=invest p (g _) k; rw [ht]
  all_goals first|omega|rw [zero_mul]
end YM.RG08.Pivot

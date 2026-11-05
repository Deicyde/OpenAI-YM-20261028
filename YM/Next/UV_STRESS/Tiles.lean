import YM.Work.B15


/-!
# A site tiling sufficient for the shell comparisons

Exterior at grid level k (points on that grid), tiling side a_k. Choose
seam aligned one level finer, separating EVEN with exterior on the grid faces
of the unshifted tiling. Works for arbitrarily large block ratios, all allowed
periods (only occupancy needs a long period).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter Analysis Extraction Around Lattice Wilson Cells
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {F : Extraction.Order}

lemma sparse (S : Schedule) (k : ℕ) {ι : Type*} [Finite ι] (f : ι → Cover) (hf : Injective f) :
    ∀ᶠ p : ℕ in atTop, Injective ((wrap (S.side k p)) ∘ f) := by
  have hp (j : Axis) (x : Cover) : ∀ᶠ p in atTop, -( (S.side k p).val : ℤ)< 2*x j ∧ 2*x j ≤ (S.side k p).val := by
    filter_upwards [S.period_strict.tendsto_atTop.eventually (eventually_gt_atTop ((2*x j).natAbs))] with p hp
    have he : (2*x j).natAbs < (S.side k p).val :=
      hp.trans_le (Nat.le_mul_of_pos_right _ (S.denominator k).property)
    omega
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun j => hp j (f i)] with p hp i j he
  exact hf (Lattice.wrap_injOn _ (hp i) (hp j) he)

lemma large_mesh (F : Extraction.Order) (k : ℕ) : ∀ᶠ i in F.fuse,k ≤ i.1 := by
  rw [Order.fused,Order.late]; exact Eventually.of_forall (fun _ : ℕ => F.mesh.cofinal.eventually (eventually_ge_atTop k))



def terrace (S : Schedule) (k : ℕ) {N : ℕ} (h : k+1≤N) (p : ℕ) : Tiling (S.side N p) :=
  let b := Cells.span S h p*((S.block k).val/2)
  { period := S.side k p
    units := S.toDepth ((Nat.le_succ k).trans h) p, kind:=.site
    widthHalf := Cells.half S k p
    even := Cells.original S k p
    base := fun _ => -(b : Per (S.side N p)) }

lemma base_coarse (S : Schedule) {N p : ℕ} (k) (h : k+1≤N) :
    (terrace S k h p).base=location S (k+1) N p (fun _ => -(↑((S.block k).val / 2):ℤ)) := by
  funext i
  rw [location,dif_pos h,Ratio.embed_wrap]
  change -((Cells.span S h p*((S.block k).val/2):ℕ):Per (S.side N p)) =
    (((Cells.span S h p • (-(↑((S.block k).val / 2):ℤ))) : ℤ) : Per (S.side N p))
  rw [nsmul_eq_mul, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_neg,Int.cast_natCast,mul_neg]

lemma buffered (S : Schedule) (k : ℕ) {N : ℕ} (h : k+1≤N) (p : ℕ) (x : Cover) :
    let T := terrace S k h p
    location S k N p x ∈ T.margin (Lattice.wrap (S.side k p) x) (T.side.val/3) := by
  intro T; let t := location S k N p x
  let v : T.Cell := Lattice.wrap _ x
  let L := (S.block k).val
  let m := Cells.span S h p
  have hL : 3≤L:=S.block_large _
  have hT : T.side.val=m*L := Work.B15.count_trans (S.toDepth h p) (S.oneStep k p) _
  have hm : 0<m := (S.toDepth h p).count.property
  let b := m*(L/2)
  have hu : 3*b ≥ m*L := by
    have hx : L ≤ 3*(L/2) := by omega
    dsimp [b]; nlinarith
  have hv : 2*b ≤ m*L := by
    have hx : 2*(L/2) ≤ L := by omega
    dsimp [b]; nlinarith
  have hp : 0 < T.side.val := T.side.property
  have he : t=T.units.root v := by unfold t; rw [location,dif_pos ((Nat.le_succ k).trans h)]; rfl
  have hz i : T.coordinated v t i=b := by
    have ht : t i-T.starts v i = (b : Per (S.side N p)) := by
      unfold Tiling.starts; rw [he]; change _-(-(b : Per _)+_)=_; abel
    unfold Tiling.coordinated; rw [ht]; exact ZMod.val_natCast_of_lt ((show b<T.side.val by omega).trans T.narrow)
  refine ⟨fun i => ?_,fun i => ?_⟩
  · change 0 < T.coordinated v t i ∧ T.coordinated v t i < _
    rw [hz]; omega
  change T.side.val/3≤T.coordinated v t i ∧ T.coordinated v t i+T.side.val/3+0 ≤ T.side.val
  rw [hz]; omega

/-- `Span` is independent of the period index. -/
def pushSite (S : Schedule) {m N : ℕ} (h : m ≤ N) (p : Cover) : Cover := Cells.span S h 0 • p

lemma location_down (S : Schedule) {m N l : ℕ} (h : m≤N) (he : N≤l) (p : Cover) (r : ℕ) :
    location S N l r (pushSite S h p)=location S m l r p := by
  unfold location; rw [dif_pos he,dif_pos (h.trans he),Ratio.embed_wrap,Ratio.embed_wrap]
  change wrap _ (Cells.span S he r • (Cells.span S h r • p))= _
  rw [smul_smul]; congr 2
  exact (Work.B15.count_trans (S.toDepth he r) (S.toDepth h r) (S.toDepth (h.trans he) r)).symm

lemma finer (S : Schedule) {m N : ℕ} (h : m≤N) (v : Cover) :
    S.gridPoint N (pushSite S h v)=S.gridPoint m v := by
  ext i; simp only [Schedule.gridPoint,WithLp.ofLp_toLp,pushSite,Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]
  rw [← mul_assoc]; exact congr_arg (fun z : ℝ => z * _) (S.embeds_scale (S.toDepth h 0))

-- Need only the expanding half of imageBudget, not CenteredBook.each

private lemma growing (H : CellHyp C F) (x : C.book.Token) :
    ∀ᶠ m in atTop, ∃ A : ℝ, 0≤A ∧ F.late (centeredBudget C x A m) := by
  rcases x with ⟨d,v⟩
  obtain ⟨m₀,hp,A,hA,η⟩ := H.centered d 1 (‖v‖+1) (by norm_num) (by positivity)
  filter_upwards [eventually_ge_atTop m₀] with m hm
  refine ⟨_,add_nonneg (mul_nonneg hA (Real.rpow_nonneg (C.S.a_pos m).le (-(d:ℝ)-1))) zero_le_one,?_⟩
  exact (η _ hm 1 (by norm_num)).mono fun i hi => hi.mono fun j hj => by
    obtain ⟨h,hj⟩ := hj; exact ⟨h,hp.trans (hm.trans h),fun o => hj v (by simp) o⟩

lemma grows {n : ℕ} (H : CellHyp C F) (v : Fin n→C.book.Token) :
    ∀ᶠ k in atTop, ∃ A : ℝ, 0≤A ∧ F.late (imageBudget v A k) := by
  classical
  let T := fun i : Fin n × Extraction.Spin.Frame => Extraction.Spin.token C.book (v i.1) i.2
  have hf := eventually_all.mpr fun i => growing H (T i)
  filter_upwards [hf] with k hk
  choose R hR hs using hk
  let Y := ∑ i,R i
  have hp i : R i ≤ Y := Finset.single_le_sum (f:=R) (fun i _ => hR i) (Finset.mem_univ i)
  refine ⟨Y,Finset.sum_nonneg (fun i _ => hR i),?_⟩
  have ht : ∀ᶠ u : ℕ×ℕ in F.fuse, ∀ i, centeredBudget C (T i) Y k u.1 u.2 := eventually_all.mpr
    fun i => (show ∀ᶠ u : ℕ×ℕ in F.fuse, centeredBudget C (T i) (R i) k u.1 u.2 from hs i).mono fun u hu =>
      Extraction.fixup C hu (hp _)
  have he : ∀ᶠ u in F.fuse, ∀ i, Around.Fit (T i) k u.1 u.2 := eventually_all.mpr fun i => by
    rw [Extraction.Order.fused]
    exact Eventually.of_forall fun r => (Around.fit (f:=F) (T i) k).mono fun p hp => hp _
  change ∀ᶠ u in F.fuse, imageBudget v Y k u.1 u.2
  exact ((ht.and he).and (large_mesh F k)).mono fun (N,p) ⟨⟨hi,hI⟩,h⟩ => ⟨h, fun x b => ⟨hi (x,b),hI (x,b)⟩⟩
end YM.Next.UVStress

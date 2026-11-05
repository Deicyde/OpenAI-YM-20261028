import YM.Planned.STATIONARY_JET_PORT.Legacy

set_option warningAsError false
/-!
# The OTHER side of existing Taylor tests

Here's a convenient way to reuse the accepted genuine `ell` and `Atom`
summability & score pricing proofs. Write their terms using `fine` but with
ratio one, no trunks, coarse leg 0 and vertical reindexing of directions.
This is simply a way to describe EXACTLY `represent` arrays for these bounds;
it is NOT a different choice of tree for the `StepData`/tested/branch or a
different path! No larger-region or branch theorem or cover identity is used
on this auxiliary ratio; projection and all reads are still on the actual
period. In particular no request that this is a schedulable subdivision
step or suggestion of proving an estimate JUST under ratio 1 for the real
step. Pays at input width with no L parameter. Use both ports e.g. for a
real Taylor remainder once just matching the zero-field component derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Filter Function Metric Lattice Matrix Push.Uniform RG Precision Tree Bid Exterior Wilson
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {c : Side} {G : Gauge}

section connector
-- reindexer (standalone use on `represent` only)
def ratio (c : Side) : Ratio c c := ⟨⟨1,by norm_num⟩,by simp⟩
lemma embedded (x : Site c) : (ratio c).embed x=x := by unfold Ratio.embed; change wrap c (1 • Lattice.lift x)=_; simp
lemma parental (x : Site c) : (ratio c).parent x=x := by
  nth_rewrite 1 [← embedded x]; exact (ratio c).embed_parent x
def arbor (c : Side) : Forest (ratio c) := Classical.choice (Tree.select (ratio c) (odd_one (α:=ℕ)))
lemma trunkless (c : Side) : (arbor c).trunks=∅ := by
  ext; unfold Forest.trunks leaf
  simp only [Finset.mem_image, Finset.mem_filter,Finset.mem_univ,true_and,parental,embedded]
  simp

def freeOf (z : Edge (Site c)) : (arbor c).Free := ⟨z,by rw [trunkless]; simp⟩
def reIndex (i : Primary c G) : Key (arbor c) G := (freeOf (i.1.1,axisEquiv.symm i.1.2), i.2)
def oldIndex (i : Key (arbor c) G) : Primary c G := ((i.1.val.1,coord i.1.val.2),i.2)
lemma there (i : Key (arbor c) G) : reIndex (oldIndex i)=i := by
  obtain ⟨⟨⟨x,j⟩,hi⟩,y⟩ := i
  unfold reIndex oldIndex freeOf; change (Subtype.mk (x,axisEquiv.symm (axisEquiv j)) _,y) = _
  congr; exact axisEquiv.symm_apply_apply j
lemma back (i : Primary c G) : oldIndex (reIndex i)=i := by
  obtain ⟨⟨x,j⟩,k⟩ := i
  exact congr_arg (fun j => ((x,j),k)) (axisEquiv.apply_symm_apply j)

def feeder (G : Gauge) (c : Side) : Positions (Primary c G) →L[ℝ] Positions (Joint (arbor c) G) :=
  (lowerCol (ι:=Primary c G)).comp (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (oldIndex i))
local notation "auxL" => (feeder G c)
lemma preFeed (x : Positions (Primary c G)) : auxL x=meetVar 0 (fun i => x (oldIndex i)) := rfl
lemma feed_norm (x : Positions (Primary c G)) : ‖auxL x‖ ≤ ‖x‖ := by
  rw [preFeed,norm_meet]; apply max_le (by simp)
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i => norm_le_pi_norm ..)
lemma fed (x : Positions (Primary c G)) : fine G (arbor c) (auxL x)=represent (tint G _ x) := by
  rw [fine,outer,preFeed,paint]
  let y : Positions (Key (arbor c) G) := fun i => x (oldIndex i)
  let H := partSpace (Primary c G) (Key (arbor c) G)
  have he : H (meetVar 0 y) = (0,y) := H.apply_symm_apply _
  simp only [ContinuousLinearEquiv.trans_apply]; unfold H y at he; rw [he]; simp only [ContinuousLinearEquiv.prodCongr_apply, map_zero,link_one]
  funext i; unfold lifting represent
  rw [show (arbor c).drape _ i=_ from (arbor c).off_tree _ (freeOf i),replica_one]
  rfl

lemma feed_unit (i : Primary c G) : auxL (bolt i) = bolt (Sum.inr (reIndex i)) := by
  unfold feeder; rw [ContinuousLinearMap.comp_apply, ← lower_bolt]
  congr 1; funext b
  change bolt i (oldIndex b)=bolt (reIndex i) b
  by_cases he : oldIndex b=i
  · rw [← he,there]; simp [bolt]
  have hh : b≠ reIndex i := fun ht => he (ht.symm ▸ back i)
  simp [bolt, he,hh]

variable {a C : ℝ} {x : Positions (Primary c G)}
lemma feed_through {F : Positions (Joint (arbor c) G) → ℝ} (hF : ContDiffAt ℝ ω F (auxL x))
    {k : ℕ} (h : Scatter (address (arbor c) G) a k F (auxL x) C) :
    let Q := F ∘ auxL
    ContDiffAt ℝ ω Q x ∧ Scatter (fun i : Primary c G => i.1.1) a k Q x C := by
  intro Q; refine ⟨hF.comp x (auxL).contDiff.contDiffAt,fun v hv j q => ?_⟩
  rw [show entry Q x j=entry F (auxL x) (Sum.inr ∘ reIndex ∘ j) from ?_]
  · exact h _ hv _ q
  unfold entry Q; rw [iter_lin_at (L:=auxL) (hF.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [comp_def]; congr; ext1 i; exact feed_unit _
end connector


variable {μ C Λ : ℝ} {p : Clip} {R : PathData G} {N : ℕ}

def dial (μ : ℝ) (N : ℕ) := weaker N (entryWidth N (ratio ⟨1,by norm_num⟩).count μ)
namespace BareRates
structure pre (G : Gauge) (μ C : ℝ) (N : ℕ) where
  Z : ℝ
  X : ℝ
  hZ : PaintSupply G N Z
  hX : SquarePay G N Z μ C X
lemma offered (G : Gauge) (μ C : ℝ) (N : ℕ) : Nonempty (pre G μ C N) := by
  obtain ⟨Z,hZ⟩ := paint_supply G N
  obtain ⟨X,hX⟩ := square_pay G N Z μ C
  exact ⟨Z,X,hZ,hX⟩
def bill (F : pre G μ C N) (p : Clip) :=
  let L := (ratio ⟨1,by decide⟩).count
  let a := entryWidth N L μ
  1+|mainCost G N F.Z F.X μ C p L| +
    (Fintype.card PlaqAxes:ℝ)*|quadCost G N F.Z F.X μ C p L| * countCost (a/2) +
    |atomCost G F.Z μ N 2| * countCost (a/2)
end BareRates

abbrev throat (c : Side) (G : Gauge) := fun i : Primary c G => i.1.1
lemma device (c : Side) (G : Gauge) : Multiplicity (throat c G) (townCost G) := by
  have hh := (town (G:=G) (arbor c)).comp (Sum.inr_injective (α:=Primary c G)|>.comp
    (show Injective (@reIndex c G) from fun i j he => (back i).symm.trans ((congr_arg oldIndex he).trans (back j))))
  exact hh

lemma symAll {ι E : Type} [Fintype ι] [Fintype E] [Nonempty E] {x : Positions ι} {H : E → Positions ι → ℝ} {l : ι → Site c}
    {v D : ℝ} (hf : ∀ i, ContDiffAt ℝ ω (H i) x) (h : ∀ i, Scatter l v N (H i) x D) :
    let T y := Patch.average fun i => H i y
    ContDiffAt ℝ ω T x ∧ Scatter l v N T x D := by
  let L : ℝ := Fintype.card E; have hl : 0 < L := by unfold L; positivity
  have hv := ContDiffAt.sum (s:=Finset.univ) fun i _ => hf i
  refine ⟨hv.const_smul L⁻¹,?_⟩
  have he := (scatter_sum (s:=Finset.univ) (fun i _ => hf i) (fun i _ => h i)).smul hv L⁻¹
  rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, abs_of_nonneg (inv_pos.mpr hl).le,
    show (Fintype.card E:ℝ)=L from rfl, inv_mul_cancel_left₀ hl.ne'] at he
  exact he

lemma bareSocket (c : Side) (A : BareRates.pre G μ C N) (h : R.Bounds p μ C Λ) {x : Positions (Primary c G)} (hx : x∈Metric.ball 0 1)
    (α : ℝ) :
    let u y := represent (tint G _ (y:Positions (Primary c G)))
    let F y := mainTerm p R (u y); let Q := draft (c:=c) α R p ∘ tint G _
    let v := dial μ N; let L := throat c G
    ContDiffAt ℝ ω F x ∧ ContDiffAt ℝ ω Q x ∧
      0<v ∧ 0 < BareRates.bill A p ∧ Scatter L v N F x (BareRates.bill A p) ∧
        Scatter L v N Q x ((1+|α|+Λ)*BareRates.bill A p) := by
  let B := arbor c; let L' := (ratio c).count; let j := feeder G c; let y := j x
  let a := entryWidth N L' μ; let v := weaker N a; let b := countCost (a/2)
  intro u F T w o
  have hh' : ‖x‖ < (1:ℝ) := by simpa using hx
  have hh : y∈Metric.ball 0 1 := mem_ball_zero_iff.mpr ((feed_norm x).trans_lt hh')
  let U (z : Positions (Joint B G)) := fine G B z
  have hU q : u q=U (j q) := (fed q).symm
  have main := main_beacons B h A.hZ A.hX y hh
  have hf := feed_through main.1 main.2
  change ContDiffAt ℝ ω F x ∧ _
  let X := mainCost G N A.Z A.X μ C p L'; let Z := quadCost G N A.Z A.X μ C p L'; let E := atomCost G A.Z μ N 2
  let n : ℝ := Fintype.card PlaqAxes
  have he : F=(fun z => mainTerm p R (U z)) ∘ j := funext fun i => by unfold F; rw [hU]; rfl
  rw [he]
  have ha : 0<a := width_positive h.width N L'; have hd : 0<w := by change 0<v; unfold v weaker; positivity
  let D := BareRates.bill A p
  have hb : 0<b := count_pos (half_pos ha)
  have H : 0<D := by change 0<1+|X|+n*|Z| *b+|E| *b; have ht : 0 ≤ n := Nat.cast_nonneg _; positivity
  have hX : X ≤ D := by
    refine (le_abs_self _).trans ?_; change |X| ≤ 1+|X|+n*|Z| *b+|E| *b
    have he : 0 ≤ n := Nat.cast_nonneg _; nlinarith [abs_nonneg E, mul_nonneg (mul_nonneg he (abs_nonneg Z)) hb.le]
  refine ⟨hf.1,?_⟩
  let P h (z : Positions (Joint B G)) := pull (h:Signed) (0:Site c) (U z)
  let Q h (z : Positions (Joint B G)) := quadratic p R (P h z)
  let R' h (z : Positions (Joint B G)) := uncut R.loop (P h z)
  let b' := address B G
  have scatter1 (s : Signed) {f' : Site c → Positions (Joint B G) → ℝ} {Q' : ℝ}
      (hz : ∀ i, ContDiffAt ℝ ω (f' i) y ∧ Beacon b' a N (f' i) (affine s 0 i) y Q') (hQ : 0 ≤ Q') :
      ContDiffAt ℝ ω (fun z => ∑ i, f' i z) y ∧ Scatter b' v N (fun z => ∑ i, f' i z) y (Q'*b) := by
    have hi : Injective (affine (R:=Per c) s 0) := fun i j h => by
      unfold affine at h; have he := add_right_cancel h; simpa using congr_arg s⁻¹.act he
    refine ⟨ContDiffAt.sum (s:=Finset.univ) (fun i _ => (hz i).1),?_⟩
    simpa only [Nat.cast_one,mul_one] using scatter (Multiplicity.injective hi) (fun i => (hz i).1) (fun i => (hz i).2) ha hQ
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hZ : n*|Z| * b ≤ D := by change _ ≤ 1+|X|+n*|Z| *b+|E| *b; have h := abs_nonneg X; nlinarith [abs_nonneg E]
  have hQ s : ContDiffAt ℝ ω (Q s) y ∧ Scatter b' v N (Q s) y D := by
    have he : Q s=fun z => ∑ i : Site c, ∑ l : PlaqAxes, quad B p R s (i,l) z := by
      funext; unfold Q quadratic; rw [Fintype.sum_prod_type]; rfl
    rw [he]
    have hz i (l : PlaqAxes) := eye B h A.hZ A.hX s (i,l) y hh
    have hh := scatter1 s (f':=fun i z => ∑ l : PlaqAxes, quad B p R s (i,l) z) (Q':=n*|Z|) (fun i => ?_) (mul_nonneg hn (abs_nonneg Z))
    exact ⟨hh.1,hh.2.mono hZ⟩
    refine ⟨ContDiffAt.sum (s:=Finset.univ) (fun l _ => (hz i l).1),?_⟩
    have h := beacon_sum (l:=b') (y:=affine s 0 i) (f:=fun l => quad B p R s (i,l)) (C:=fun _=>|Z|) (a:=a) (s:=Finset.univ) (fun l _ => (hz i l).2.mono (show Z ≤ |Z| from le_abs_self _))
      (fun l _ => (hz i l).1)
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h; exact h
  have hR := symAll (fun i => (hQ i).1) (fun i => (hQ i).2)
  have hg := feed_through hR.1 hR.2
  let fC y := secondTerm p R (u y)
  have he : fC=(fun z : Positions (Joint B G) => Patch.average fun i => Q i z) ∘ j := by
    funext; unfold fC secondTerm Q; rw [hU]; rfl
  have hP : ContDiffAt ℝ ω fC x ∧ Scatter o w N fC x D := he.symm ▸ hg
  have hΛ := hasInheritance h
  have hE : |E| *b ≤ D := by change |E| *b ≤ 1+|X|+n*|Z| *b+|E| *b; have h := abs_nonneg X; nlinarith [mul_nonneg (mul_nonneg hn (abs_nonneg Z)) hb.le]
  have hhQ s : ContDiffAt ℝ ω (R' s) y ∧ Scatter b' v N (R' s) y (Λ*D) := by
    unfold R' uncut
    let g i (z : Positions (Joint B G)) := ∑' k,(R.loop k).unmasked (P s z) i
    have hf i : ContDiffAt ℝ ω (g i) y := label_analytic B R.loop h.width h.two s A.hZ i y hh
    have hg i : Beacon b' a N (g i) (affine s 0 i) y (Λ*E) := atom_beacon B s h.width h.two A.hZ y hh i
    have he := scatter1 s (f':=g) (fun i => ⟨hf i,(hg i).mono (mul_le_mul_of_nonneg_left (le_abs_self _) hΛ)⟩) (mul_nonneg hΛ (abs_nonneg E))
    exact ⟨he.1,he.2.mono (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hE hΛ)⟩
  have hs := symAll (fun i => (hhQ i).1) (fun i => (hhQ i).2)
  have hg := feed_through hs.1 hs.2
  let fL z := Precision.loop R (u z)
  have he : fL=(fun z : Positions (Joint B G) => Patch.average fun i => R' i z) ∘ j := by
    funext; unfold fL Precision.loop R' P; rw [hU]; rfl
  have hL : ContDiffAt ℝ ω fL x ∧ Scatter o w N fL x (Λ*D) := he.symm ▸ hg
  have hs := hP.1.const_smul α
  refine ⟨hs.add hL.1, hd, H, hf.2.mono hX, ((hP.2.smul hP.1 α).add hs hL.1 hL.2).mono ?_⟩
  change |α| *D+Λ*D ≤ (1+|α|+Λ)*D
  nlinarith
end YM.Planned.JetPort

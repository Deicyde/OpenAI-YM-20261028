import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pedi

/-!
# All Arm A and S power consumptions, actual analytic in grafted neighborhood

All-order determinant edges. Expense charges are unpacked. May use larger
radius than q=s (1/2) even though differentiated, retaining any rate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen    Vine Tablet Metric
variable {v z r Q s y η γ : ℝ} {j m n d B : ℕ} {x : E}
namespace Vine
variable (D : Window (along (G:=G) S) B) (A : E→ Mat f G) (hp : ∀ x, Thin (along S) (along S) (A x) (B/2))
    (hx : Tablet j γ v z A (along S) (along S) x) (h : Allow (A x) (along S) m η r Q) (ht : Torch η r Q)
    (hb : γ≤retain η r Q) (ho : 4≤B)

include hx h ht
lemma e_prefix (y : ℝ) (hy : y∈Set.Icc (0:ℝ) 1) :
    ∀ n i k, ContDiffAt ℝ (↑j) (fun z : E × ℝ=> aSeq D (A z.1) z.2 n i k) (x,y) := by
  let Y (z:E×ℝ) := glide (A z.1) z.2
  intro n; have hh := joyful D A h hx ht y hy
  match n with
  | 0 => exact fun i j=> ((hx.singular i j).smooth.comp (f:=Prod.fst) (x,y) contDiffAt_fst).sub contDiffAt_const
  | 1 => exact fun i j=> (hh ..).2
  | k+2 => exact fun i l=> (((per_entry Y (fun x=> D.pad (Y x)) (x,y) i l (fun j=> (hh ..).1) (fun j=> (hh ..).2)).sub contDiffAt_const).neg)

omit ht in
lemma s_prefix (y : ℝ) : ∀ n i k, ContDiffAt ℝ (↑j) (fun z : E × ℝ=> sSeq D (A z.1) z.2 n i k) (x,y) := by
  have ht i j : ContDiffAt ℝ (↑_ : WithTop ℕ∞) (fun z=> D.pad (A z) i j) x := orbit D A (fun i j=> (hx.singular i j).smooth)
    (fun i=> isUnit_det_of_right_inverse (h.sub (Embedding.subtype (·∈D.take i))).initial.1) i j
  let sV i := D.flawed (A i)
  have hv i l : ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun z=> sV z i l) x := by
    refine (per_entry A (fun z=> D.frameMean (A z)) x i l (fun k => (hx.singular ..).smooth) ?_).sub contDiffAt_const
    exact fun k=> ((ht k l).add (ht l k)).const_smul (1/2:ℝ)
  intro n i k; cases n
  · exact (hv i k).comp (f:=Prod.fst) (x,y) contDiffAt_fst
  exact (contDiffAt_snd.smul ((hv i k).comp (f:=Prod.fst) (x,y) contDiffAt_fst)).neg

include hp hb ho
variable [FiniteDimensional ℝ E]

lemma glacierA (p : Ledger f 3) :
    let F:=1+(v+1); let h:=facePrice j B m F (payE η r Q m); let t:= tidal γ F h B
    let n:= (Fintype.card G.ColorIndex:ℝ); let d:= z+driftP j z
    Brush j (cap S B 3 p (n^4*((v+1)*(h*t))) (n*t)) ((↑(p.1+3:ℕ):ℝ)*d) (fun i=> ArmA D (A i) p) x := by
  intro F h' t Q' d
  let l n := match n with
    | 0 => v+1
    | 1 => h'
    | _+2 => t
  have hf y (hv : y∈Set.Icc (0:ℝ) 1) n : Tablet j (γ/2) (l n) d (fun i=> aSeq D (A i) y n) (along S) (along S) x := by
    have hF:= h.glide ht.hv ht.hQ y hv
    have hG:=thunder hx y hv
    have hp:=wavesP D hG hF hb
    match n with
    | 0 => exact (hx.joined (Tablet.fixed (x:=x) _ (one_pay ..) hx.scale zero_le_one hx.pos).mirror).tilt le_rfl
                       (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hx.pos)) hp.scale (half_le_self hx.scale)
    | 1 => exact (padjets D hG hF hb).tilt (le_refl _) (le_add_of_nonneg_left hx.pos) hp.scale (half_le_self hx.scale)
    | n+2 => exact hp.mirror
  have hJ (x : E) y n : Thin (along S) (along S) (aSeq D (A x) y n) (3*B) := by
    rintro i j he; match n with
    | 0 =>
      have hi : i ≠ j := by rintro rfl; simp at he
      rw [aSeq,Matrix.sub_apply,hp x _ _ (by omega)]; simp [hi]
    | 1 => exact (D.thin _) _ _ (by omega)
    | n+2 => exact (Itinerary.opposite _ (D.stencil _ (Window.Thin.glides _ (hp x) y))) i j (by omega)
  rcases p with ⟨k,v',p⟩
  have hy := plurality (n:=k+3) (fun x => aSeq D (A x)) l (fun k _=> (hf 0 (Set.left_mem_Icc.mpr zero_le_one) k).basis)
    (fun y hy n _ i j=> ⟨(hf y hy n).singular i j,e_prefix D A hx h ht y hy n i j⟩) (fun x s j _=>hJ x s j)
    (add_nonneg hx.pos (mul_nonneg (Nat.cast_nonneg _) hx.pos)) v' p
  apply hy.climb _ le_rfl; unfold cap; dsimp only; split
  next h =>
    rw [count_mul,count_mul]; change Q'^(k+3+1)*((v+1)*(h'*Pulse.Itinerary.tally (n:=k+1) (fun _=>t))) ≤ _
    rw [one_hut]; exact le_of_eq (by ring)
  exact le_rfl

omit ht in
lemma glacierS (hP : ∀ x, (A x).IsHermitian) (p : Ledger f 1) :
    let s:= payE η r Q m; let F:= facePrice j B m v s; let t:= tidal γ v F B
    let w:=v*(token j v s*t); let Q':= (Fintype.card G.ColorIndex:ℝ); let d:=z+(driftP j z + (z+driftP j z))
    Brush j (cap S B 1 p (Q'^2*w) (Q'*w)) ((↑(p.1+1:ℕ):ℝ)*d) (fun i=> ArmS D (A i) p) x := by
  intro s F t w Q' d
  have hv:= debris D hx h hb hP
  rcases p with ⟨k,u,p⟩
  have hf y (hy : y∈Set.Icc (0:ℝ) 1) n : Tablet j (γ/2) w d (fun i=> sSeq D (A i) y n) (along S) (along S) x := by
    match n with
    | 0 => exact hv
    | _+1 => exact (hv.scalar y).mirror.tilt (mul_le_of_le_one_left hv.basis ((Real.norm_of_nonneg hy.1).trans_le hy.2))
                  le_rfl hv.scale le_rfl
  have hJ x y n : Thin (along S) (along S) (sSeq D (A x) y n) (3*B) := by
    have ht:= effects D (A x) (hp x) ho; cases n
    · exact ht
    exact Itinerary.opposite _ (iso _ ht y)
  have he := plurality (n:=k+1) (fun i=> sSeq D (A i)) (fun _ => w) (fun _ _=> hv.basis)
    (fun y hy n _ i j' => ⟨(hf y hy n).singular i j', s_prefix D A hx h y n i j'⟩) (fun x s i _=> hJ x s i) hv.pos u p
  apply he.climb _ le_rfl; unfold cap; dsimp only; split
  next h => rw [one_hut]; unfold Q'; exact le_of_eq (by ring)
  exact le_rfl
end Vine
end YM.ConnectedActivityE6.Blaze

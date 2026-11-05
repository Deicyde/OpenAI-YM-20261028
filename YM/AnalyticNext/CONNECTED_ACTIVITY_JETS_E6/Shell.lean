import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Room
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sector
import YM.Next.PHASE.Roots

/-!
# Active/frozen shell on the same F and V

Hard sectors and every Plot still use actual tags. For the annulus
part of a compulsory packet don't attempt a single gauge orientation
valid on the whole torus. `Shell.Interior` is for near the site. All-field
bounds on the *frozen* influences allow spending on the Gaussian
corrections after optional h's outside the packet removed some defaults.
Never infer Chart before the slice. Post-L prices unless stated.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint Precision
open SectorMeasure  Oriented Next.Fluctuations  Tags Channel
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

namespace Shell
/-- Coarse scale center and endpoints. -/
def atEdge (S : StepData c f) (x : Bond f) : Site c := S.ratio.parent x.1

def ends (S : StepData c f) (x : Bond f) := (Pressure.pinPos x).image S.ratio.parent

def distAt (S : StepData c f) (x : Bond f) (y : Site c) := separation y (atEdge S x)

abbrev Inside (x : Site c) (A : Stores S) (n : ℕ) : Prop := x∈A.dome n

lemma touch_extend {A : Stores S} {x y : Site c} {u v : ℕ} (he : Inside x A u) (hf : u+separation x y ≤ v) :
    Inside y A v := by
  obtain ⟨z,hz,h⟩ := halo_spec.mp he
  exact halo_spec.mpr ⟨z,hz,(separation_triangle z x y).trans (by omega)⟩

lemma clear {A : Stores S} {x y : Site c} {u v : ℕ} (he : ¬Inside x A v) (hf : u+separation x y ≤ v) :
    ¬Inside y A u := fun h => he (touch_extend h (by rwa [separation_comm y]))

variable (A : Stores S)

lemma stride (p : Bond f) {x : Site c} (h : x∈ends S p) : distAt S p x ≤ 1 := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp h
  unfold distAt atEdge
  rcases mem_insert.mp hv with h|h
  · subst v; simp
  rw [mem_singleton.mp h,separation_comm]; exact Work.E03.parent_step S p.1 p.2

lemma center_end (p : Bond f) : atEdge S p ∈ ends S p := mem_image_of_mem _ (mem_insert_self ..)

def frozen (A : Stores S) (B : ℕ) (p : Bond f) := ¬ Disjoint (A.dome (10*B)) (ends S p)

def active (F : Forest S.ratio) (A : Stores S) (B : ℕ) (p : Bond f) := p ∉ F.trunks ∧ ¬ frozen A B p

lemma active_far {F : Forest S.ratio} {B : ℕ} (p : Bond f) (h : active F A B p) :
    ¬ Inside (atEdge S p) A (10*B) := fun he => h.2 ((not_disjoint_iff).mpr ⟨_,he,center_end p⟩)

lemma far_active (F : Forest S.ratio) {B : ℕ} (p : Bond f) (h : ¬ Inside (atEdge S p) A (10*B+1)) (hp : p ∉ F.trunks) :
    active F A B p := by
  refine ⟨hp,fun he => ?_⟩
  obtain ⟨v,hv,ht⟩ := not_disjoint_iff.mp he
  exact h (touch_extend hv (Nat.add_le_add_left (stride p ht) _))



/-- Under manifest flags or a Wide constraint supplying them at the
required halo sites. No differentiating any actual flag. -/
def Clean (V : Config G c) (x : ℝ) (o : Site c) (B : ℕ) : Prop := ∀ y : Site c,
    separation o y ≤ B → y ∉ RG.flags (Pressure.temp x) V

lemma Clean.toll {V : Config G c} {x : ℝ} {o : Site c} {B : ℕ} (h : Clean V x o B) {b : Cell c}
    (he : separation o b.1 ≤ B) : toll V b ≤ Pressure.temp x := by
  apply le_of_not_gt; intro hv
  exact h _ he ((flags_spec ..).mpr ⟨b,Work.E01.base_touched _,hv⟩)

lemma Clean.kept {P : Teller G} {T : Tube G S} {V : Config G c} {x : ℝ} (hR : Room P S T x)
    {o : Site c} {B : ℕ} (h : Clean V x o B) (y : Site c) (hy : separation o y+radiusB x/25 ≤ B) :
      PathData.kept T.low (Pressure.temp x) y V := by
  intro p
  by_cases hk : Pressure.temp x*Real.exp ((separation y p.1:ℝ)/T.low.relaxation) < 2
  · have he := hR.laneV _ hk; have hh : separation o p.1 ≤ B := (separation_triangle o y p.1).trans (by omega)
    exact le_trans (h.toll (b:=p) hh) (le_mul_of_one_le_right (temp_nonneg x)
      (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) T.low.radius_pos.le)))
  exact (G.chord_le_two _).trans (le_of_not_gt hk)

lemma Clean.turn {o : Site c} {s : Signed} {B : ℕ} {x : ℝ} {V : Config G c} (h : Clean V x (s.act o) B) :
    Clean (pull s 0 V) x o B := by
  intro y he hh; refine h (s.act y) (by rwa [separation_signed]) ?_
  rw [← Work.H03.flags_send s 0]; exact (affine0 _ _ ▸ mem_image_of_mem (affine s 0) hh)

lemma Clean.shrink {o v : Site c} {B D : ℕ} {x : ℝ} {V : Config G c} (h : Clean V x o B)
    (hi : separation o v+D ≤ B) : Clean V x v D := by
  intro y he; exact h _ ((separation_triangle o v y).trans (by omega))

lemma clean_far {x : ℝ} (V : Config G c) {o : Site c} {B : ℕ} (h : A.flags = RG.flags (Pressure.temp x) V)
    (he : ¬ Inside o A B) : Clean V x o B := by
  intro y hy H; apply he; exact halo_spec.mpr
    ⟨y,mem_union_right _ (h.symm ▸ H),by rwa [separation_comm]⟩

lemma clean_halo {x W d} {U : Config G f} {k : S.Choices} {V : Config G c} {o : Site c} {B E : ℕ}
    (h : Tags.Wide A d U k V x W) (hi : ¬Inside o A B) (hf : Inside o A E) (he : E+B ≤ d) : Clean V x o B := by
  intro y hy H; apply hi
  exact halo_spec.mpr ⟨y,mem_union_right _ ((h.flags y (touch_extend hf (by omega))).mpr H),by rwa [separation_comm y]⟩

section moves
variable {P : Teller G} {T : Tube G S} {A}

lemma cops_at (G : Gauge) (P : Teller G) (L : Side) : ∃ C : ℝ, 0 < C ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (x : ℝ), S.patch.L=L → Room P S T x →
    ∀ F : Forest S.ratio, ∀ (U : Config G f) (V : Config G c) (k : S.Choices), SliceSet S F U →
      ∀ i : Bond f, Pressure.usable S U (atEdge S i) k → Bid.Cops (S:=S) U V (S.prediction U k) i C := by
  obtain ⟨C,hC,H⟩ := Work.E02.answer G L P.j P.bind
  exact ⟨C,hC,fun _ _ _ h hr F U V k hu i hi => H _ _ _ hr.accepted.knobs h hr.accepted.atStep hr.larger.2.1 hr.larger.2.2 F U hu V i k hi⟩

/-- Number of sites only in a precommitted macro-box bound. -/
def macroPrice (S : Patch) : ℝ := (2*(Pressure.macroR S:ℝ)+1)^4 * (Fintype.card PlaqAxes:ℝ)

def shellPrice (P : Patch) (C W : ℝ) : ℝ := C*macroPrice P / 2 + 2*W

lemma shellPrice_pos (P : Patch) {C W : ℝ} (hC : 0 ≤ C) (hW : 0 < W) : 0 < shellPrice P C W := by
  unfold shellPrice macroPrice; positivity

/-- Local on ONE V (which may have distant flags); no need for a shared-store
choice beyond same k, orientation. -/
structure Interior (S : StepData c f) (x W : ℝ) (o : Site c) (B : ℕ) (U : Config G f)
    (k : S.Choices) (V : Config G c) : Prop where
  list y : separation o y ≤ B → 0 < S.patch.frameMass S.kernel (expandAt (S.ratio.embed y) U) (k.1 y)
  fine (i : Cell f) : separation o (S.ratio.parent i.1) ≤ B → toll U i ≤ Pressure.fiery G x S.patch.L/2
  bond (b : Bond c) : separation o b.1 ≤ B → wire (S.prediction U k) V b ≤ 2*W*Pressure.fiery G x S.patch.L

lemma Interior.from_wide (U : Config G f) (V : Config G c) (k : S.Choices) (o : Site c) {x W a b B}
    (h : Tags.Wide A b U k V x W) (hi : Inside o A a) (hv : a+B ≤ b) (hp : ¬Inside o A B) :
    Interior S x W o B U k V := by
  have hk w (hw : separation o w ≤ B) : Inside w A b := touch_extend hi
    ((Nat.add_le_add_left hw a).trans hv)
  constructor
  · intro y hy; exact h.frame_active _ (hk _ hy)
  · intro i he
    let u := S.ratio.parent i.1
    have hu : u∈startPos S i := Packets.contains S (.inl i)
    apply (h.s i (Finset.not_disjoint_iff.mpr ⟨u,hk _ he,hu⟩)).2
    intro hA; apply hp
    exact halo_spec.mpr ⟨u,mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨i,hA,hu⟩)),
      (separation_comm ..).trans_le he⟩
  intro b hb; have he : b.1∈pinPos b := mem_insert_self ..
  apply (h.n b (Finset.not_disjoint_iff.mpr ⟨b.1,hk b.1 hb,he⟩)).2
  intro ha; apply hp
  exact halo_spec.mpr ⟨b.1,mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨b,ha,he⟩)),
    (separation_comm ..).trans_le hb⟩

lemma Interior.of_actual {x W : ℝ} {B : ℕ} (U : Config G f) (V : Config G c) (k : S.Choices) (o : Site c)
    (h : SectorMeasure.Seeded A U k V x W) (hk : SectorMeasure.Alive S U k) (hp : ¬Inside o A B) :
    Interior S x W o B U k V := by
  constructor
  · exact fun i _ => SectorMeasure.listed_of_alive hk i
  · intro i hi; apply (h.fine i).2; intro he
    exact hp <| halo_spec.mpr ⟨_,mem_union_left _ (mem_union_left _ (mem_biUnion.mpr
      ⟨i,he, Packets.contains S (.inl i)⟩)),(separation_comm ..).trans_le hi⟩
  intro b hb; apply (h.coarse b).2; intro ha
  exact hp <| halo_spec.mpr ⟨_,mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
    ⟨b,ha,Packets.contains S (.inr (.inl b))⟩)),(separation_comm ..).trans_le hb⟩



lemma Interior.displacement {x W : ℝ} (hW : 0 ≤ W) (r : Room P S T x) {U : Config G f} {V : Config G c}
    {k : S.Choices} {e : Bond f} {C : ℝ} (hC : 0 < C)
    (cops : usable S U (atEdge S e) k → Bid.Cops (S:=S) U V (S.prediction U k) e C)
    (h : Interior S x W (atEdge S e) (radiusB x/4) U k V) :
    G.chord (U e * (replica S.ratio V e)⁻¹) ≤ shellPrice S.patch C W * Pressure.fiery G x S.patch.L := by
  let B := radiusB x; let t := Pressure.fiery G x S.patch.L; let y := atEdge S e
  have hz : 0 < t := r.fiery
  have hrB := r.frame
  have hh : usable S U y k := fun z he => h.list _ ((Work.E08.separation_box_add y he).trans (by omega))
  have hv : port S y U ≤ macroPrice S.patch * (t/2) := Work.E08.port_le y (B/4) _ (half_pos hz).le h.fine y
    (by unfold B; rw [separation_self]; omega)
  have hp : wire (S.prediction U k) V (y,e.2) ≤ 2*W*t := h.bond (y,e.2) (by simp [y])
  have hq : 0 ≤ 2*W*t := by positivity
  apply (cops hh).trans
  calc
    _ ≤ C*(macroPrice S.patch*(t/2))+2*W*t := add_le_add (mul_le_mul_of_nonneg_left hv hC.le) (by split <;> assumption)
    _ = _ := by unfold shellPrice t; ring
end moves
end Shell
end YM.ConnectedActivityE6

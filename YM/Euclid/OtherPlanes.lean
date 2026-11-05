import YM.Euclid.Stress

/-!
# RP on transported planes, in the all-spectator quotient

Planes parametrized by translation and O(4), use any a for the seam to move.
Give a change of basis useful under different choices of coordinates for words.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Table
open Function Set Filter Analysis Word
open scoped Topology BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} (T : Table L)

abbrev Species (S : Table L) := E4 × S.Tag
abbrev ClassWords (S : Table L) := List (Species S)

namespace ClassWords
variable {n : ℕ} (R : S.Rotation) (H : S.RealSpin) (a : Axis) (K : Ortho) (b : E4)

def lifted (s : L.Word) : ClassWords S := s.map fun x => (x.1,S.classTokens x.2)
def read (v : ClassWords S) := S.useAt T (points fun i : Fin v.length => (v.get i).1) fun i => (v.get i).2

def independent (v : ClassWords S) := (v.map Prod.fst).Nodup

lemma via (v : ClassWords S) (n) (h : n=v.length) (x : Points n) (w : Fin n → S.Tag)
    (he : ∀ i, v.get (Fin.cast h i)=(x i,w i)) : v.read T=S.useAt T x w := by
  subst n; unfold read; congr 1
  · exact PiLp.ext fun i => congr_arg Prod.fst (he i)
  exact funext fun i => congr_arg Prod.snd (he i)

lemma read_lift (hp : T.Symmetric) (hr : T.respects S) (w : L.Word) (h : distinct w) : read T (lifted (S := S) w)=T.expect w := by
  rw [via T _ w.length (by simp [lifted]) (positions w) (S.classTokens ∘ tokens w),S.at_project T hp hr h]; rfl
  simp [lifted,positions,tokens]

def pre (x : E4) := Ortho.move K⁻¹ (x-b)
def beyond (v : ClassWords S) := independent v ∧ ∀ p ∈ v, 0 < pre K b p.1 a

def across (v : ClassWords S) := v.map fun p => (Ortho.move K p.1+b, R.label K p.2)
def goBack (v : ClassWords S) := v.map fun p => (pre K b p.1, R.label K⁻¹ p.2)

lemma across_before {P} (h : R.Laws P H) (v : ClassWords S) : across R K b (goBack R K b v)= v := by
  have he p : R.label K (R.label K⁻¹ p)=p := by
    rcases p with ⟨x,y⟩
    unfold Table.Rotation.label
    simp [← h.group,h.fixes]
  simp [across,goBack,List.map_map,Function.comp_def,pre,he,List.map_id'']

lemma preserves (h : R.Oriented T) (hu : T.Homogeneous) (v : ClassWords S) (hi : independent v) :
    read T (across R K b v)=v.read T := by
  let x := points fun i : Fin v.length => (v.get i).1
  let w : Fin v.length → S.Tag := fun i => (v.get i).2
  have he : x ∈ conf v.length := by
    have hh := List.nodup_ofFn.mp (show (List.ofFn (fun i : Fin v.length => (v.get i).1)).Nodup from
      (show List.ofFn (fun i : Fin v.length => (v.get i).1) = (v.map Prod.fst) by
        change List.ofFn (Prod.fst ∘ v.get) = _; rw [← List.map_ofFn,List.ofFn_get]) ▸ hi)
    exact hh
  let k := Points.move K x
  rw [via T _ v.length (by simp [across]) (Points.across b k) (R.label K ∘ w)]
  · change _ = S.useAt T x w
    rw [← h _ _ _ he K]
    let y := R.label K ∘ w
    exact hu _ k (Points.move_in K he) b fun i => ⟨(y i).1,S.representative (y i).1 (y i).2⟩
  simp [across,k,x,w]

def axis (v : ClassWords S) := v.reverse.map fun p =>
    (Ortho.move (Signed.reflect a) p.1, (⟨p.2.1,S.adj H _ a p.2.2⟩ : S.Tag))

def adjoint (v : ClassWords S) := across R K b (axis H a (goBack R K b v))

lemma axis_at (s : L.Word) : axis H a (lifted s)=lifted (reflect s a) := by
  unfold axis lifted; simp only [List.map_reverse,List.map_map, reflectedPoint]
  rfl

def tests : Prop := ∀ n (w : Fin n → ClassWords S), (∀ i, (w i).beyond a K b) →
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, star (c i) * c j * read T (adjoint R H a K b (w i) ++ w j)

theorem transported {P : DiffPlan S} (hx : T.Hierarchy) (hs : R.Laws P H)
    (hu : R.Oriented T) (hr : T.respects S) : tests T R H a K b := by
  intro n W Hm c
  have hp (k : ClassWords S) : ∃ v : L.Word, lifted v = k := by
    induction k with
    | nil => exact ⟨[],rfl⟩
    | cons x s ih =>
      obtain ⟨v,rfl⟩ := ih
      rcases x with ⟨y,d,z⟩; obtain ⟨B,rfl⟩ := S.onto d z
      exact ⟨(y,⟨d,B⟩)::v,rfl⟩
  choose vo ho using fun i => hp (goBack R K b (W i))
  have he i : Positive (vo i) a := by
    constructor
    · have H (x y : E4) (e : pre K b x=pre K b y) : x=y := sub_left_injective (b:=b) ((Ortho.move_injective _) e)
      have hh := ((Hm i).1).map (f := pre K b) H
      have hR : List.map Prod.fst (vo i) = ((W i).map Prod.fst).map (pre K b) := calc
        _ = List.map Prod.fst (lifted (S := S) (vo i)) := by simp [lifted]
        _ = _ := by rw [ho]; simp only [goBack,List.map_map];rfl
      exact locations.mpr (hR ▸ hh)
    intro s hP
    have ht : (s.1,S.classTokens s.2) ∈ lifted (vo i) := List.mem_map.mpr ⟨s,hP,rfl⟩
    rw [ho] at ht
    obtain ⟨p,hp,Hs⟩ := List.mem_map.mp ht
    rw [← (Prod.mk.inj Hs).1]; exact (Hm i).2 p hp
  have hq (i : Fin n) : across R K b (lifted (vo i)) = W i := by rw [ho,across_before _ H _ _ hs]
  have hj i j : read T (adjoint R H a K b (W i) ++ W j)=T.gram a (vo i) (vo j) := by
    unfold adjoint
    rw [← ho,axis_at, ← hq j,show across R K b (lifted (reflect (vo i) a)) ++ _ =
      across R K b (lifted (reflect (vo i) a ++ vo j)) by simp only [across,lifted,List.map_append]]
    have hh := twoSides (he i) (he j)
    rw [preserves T R _ _ hu hx.translations, read_lift T hx.laws.toSymmetric hr _ hh]; rfl
    unfold independent lifted; rw [List.map_map]; exact locations.mp hh
  simp_rw [hj]; exact hx.positive _ _ _ he c
end ClassWords
end YM.Table

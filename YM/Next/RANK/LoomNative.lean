import YM.Next.RANK.Bird
import YM.Next.RANK.LoomBox
import YM.Work.E08



/-! # Native origin fits, for the source before any tours -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Lattice Wilson RG Source Function Set Beamer CellsInt 
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {b d : ℕ} {o : Site n}

def patch (R : ℕ) (o : Site n) := halo R {o}
lemma doors (x : Site n) : x∈patch b o ↔ separation o x ≤ b := by simp [patch,halo_spec]
lemma village_le (x : Cover) (hx : x∈box b) : wrap n x+o∈patch b o := doors _ |>.mpr (Work.E08.separation_box_add _ hx)
lemma patch_eq : patch b o = (box b).image (fun x => wrap n x+o) := by
  ext x; constructor
  · intro hx; refine Finset.mem_image.mpr ⟨_,Work.E08.lift_mem_box ((doors x).1 hx), by rw [wrap_lift,sub_add_cancel]⟩
  intro hx; obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx; exact village_le y hy
lemma borne (h : 2*(b+1)<n.val) (u : Cover) (hu : u∈ box b) : lift (wrap n u)=u := lift_eq_iff.mpr ⟨rfl,by
  intro i; have he := (box_test.mp hu).1 i; have hx := (box_test.mp hu).2 i; omega⟩
lemma edges_fits (h : 2*(b+1)<n.val) {x : Site n} {i} (hx : x∈patch b o) :
    lift (x+step i - o)= lift (x-o) + step i := by
  let u:= lift (x-o)
  have hp : u∈box b := Work.E08.lift_mem_box ((doors x).1 hx)
  apply lift_eq_iff.mpr
  exact ⟨by rw [map_add,wrap_step,wrap_lift];abel,fun j => by
    have hh : -(b:ℤ) ≤ u j := (box_test.mp hp).1 j
    have hv := (box_test.mp hp).2 j; change - (n.val:ℤ) < 2*(u+step i : Cover) j ∧ _; change u∈box b at hp
    change _ ∧ 2*(u+step i : Cover) j ≤ n.val; simp only [Pi.add_apply,step_apply]; split <;> omega⟩

def Room (o : Site n) (b : ℕ) : Finset (Edge (Site n)) := Finset.univ.filter fun e => e.1∈patch b o ∧ e.1+step e.2∈patch b o
abbrev Dim (o : Site n) (b : ℕ) := ↥(Room o b)
lemma broad (o : Site n) (b : ℕ) : (Room o b).card ≤ (b+b+1)^4*4 := by
  let Y:= (patch b o) ×ˢ (Finset.univ : Finset Axis)
  apply le_trans (Finset.card_le_card (show Room o b ⊆ Y from fun _ h => Finset.mem_product.mpr ⟨(Finset.mem_filter.mp h).2.1,Finset.mem_univ _⟩))
  simp only [Y,patch_eq, Finset.card_product,Finset.card_univ,Fintype.card_fin]
  refine Nat.mul_le_mul_right 4 (le_trans (Finset.card_image_le) ?_); simp [Corona.box_size]

def edgeAt (u : Cover) (o : Site n) (i : Axis) : Edge (Site n) := (wrap n u+o,i)
def register (h : 2*(b+1)<n.val) (x : Dim o b) : UsedEdges (box b) :=
  ⟨(lift (x.val.1-o),x.val.2),by
    obtain ⟨hx,h₀⟩ := (Finset.mem_filter.mp x.property).2
    exact ⟨Work.E08.lift_mem_box ((doors _).mp hx),by dsimp; rw [← edges_fits h hx]; exact Work.E08.lift_mem_box ((doors _).mp h₀)⟩⟩
@[simp] lemma publish (h : 2*(b+1)<n.val) (x : Dim o b) : edgeAt (register h x).val.1 o (register h x).val.2=x.val := by unfold edgeAt register; simp

def reads (x : UsedEdges (box b)) (o : Site n) : Dim o b := ⟨edgeAt x.val.1 o x.val.2, by
  rcases x with ⟨⟨y,j⟩,h,g⟩; change y+step j∈box b at g
  have hx := village_le (o:=o) _ g; rw [map_add,wrap_step,add_right_comm] at hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,village_le _ h,hx⟩⟩

variable (U : Config G n) (b)

def fingers (o : Site n) (x : Site n) := leaves (expandAt o U) (lift (x-o))
def spine (o : Site n) : Links (Per n) G.El := gauge (fingers U o) U

lemma nerves (o : Site n) (h : 2*(b+1)<n.val) (x : Cover) (hx : x∈box b) :
    fingers U o (wrap n x+o)=leaves (expandAt o U) x := by rw [fingers,add_sub_cancel_right,borne h x hx]
lemma spine_patch (o : Site n) (h : 2*(b+1)<n.val) : Agrees (box b) (expandAt o (spine U o)) (central (expandAt o U)) := by
  rintro ⟨x,i⟩ h₁ h₂; unfold spine; rw [expandAt_gauge]; unfold Lattice.gauge central
  dsimp only; change x∈box b at h₁; change x+step i∈box b at h₂
  rw [nerves b U o h x h₁,nerves b U o h (x+step i) h₂]; rfl

def registered (o : Site n) (p : Turn b) := used (expandAt o U) p
lemma registering (h : 2*(b+1)<n.val) (o : Site n) (p : Turn b) :
    registered b U o p=faceValue (spine U o) (wrap n p.val.1 + o,p.val.2) := by
  change travel (central (expandAt o U)) p.val.1 (square p.val.2.val.1 p.val.2.val.2)=travel (spine U o) _ (square p.val.2.val.1 p.val.2.val.2)
  let v := square p.val.2.val.1 p.val.2.val.2
  change travel _ _ v = travel _ _ v
  calc
    _ = travel (expandAt o (spine U o)) _ v := Eq.symm (travel_local p.val.1 v (expandAt o (spine U o)) (central (expandAt o U)) (fun e he hh => spine_patch b U o h _ (face_patch p e.1 he) (face_patch p _ hh)))
    _ = _ := travel_at ..
lemma heart (h : 2*(b+1)<n.val) (o : Site n) (p : Dim o b) : spine U o p.val=central (expandAt o U) (register h p).val := by
  conv_lhs => rw [← publish h p]
  exact spine_patch b U o h _ (register h p).property.1 (register h p).property.2
lemma chords (τ) (h : Healthy τ (patch b o) U) (hB : 2*(b+1)<n.val) (p : Turn b) : G.chord (registered b U o p) ≤ τ := by
  rw [registering b U hB]; unfold spine; rw [Lattice.face_gauge, G.chord_conj]
  refine le_of_not_gt fun H => Finset.disjoint_left.mp h (village_le (o:=o) _ (faceOrigin p)) ?_
  rw [flags_spec]; exact ⟨_,List.mem_toFinset.mpr List.mem_cons_self,H⟩

def curl (τ) (o : Site n) (p : Turn b) := (τ:ℝ)⁻¹ • G.curvature (registered b U o p)
lemma reads_face (o : Site n) (x : Turn b) : LocalOn ↑(patch b o) fun U : Config G n => registered b U o x := by
  intro V W hh; unfold registered used central
  have ha : Agrees ↑(box b) (expandAt o V) (expandAt o W) := by
    rintro ⟨y,i⟩ he hv
    apply hh (edgeAt y o i) (village_le y he)
    have hf := village_le (o:=o) _ (show y+step i∈box b from hv); rw [map_add,wrap_step,add_right_comm] at hf
    exact hf
  dsimp only; rw [Lattice.face_gauge,Lattice.face_gauge]
  have he : leaves (expandAt o V) x.val.1=leaves (expandAt o W) x.val.1 := travel_local _ _ _ _ fun i hi hj => ha _ (village _ (faceOrigin x) _ hi) (village _ (faceOrigin x) _ hj)
  rw [he, show faceValue (expandAt o V) x.val=faceValue (expandAt o W) x.val from travel_local _ _ _ _ (by intro i hi hk; exact ha _ (face_patch x _ hi) (face_patch x _ hk))]
lemma read_cont (o : Site n) (p : Turn b) : Continuous (fun U : Config G n => registered b U o p) := by
  unfold registered used central; simp_rw [Lattice.face_gauge]
  unfold leaves faceValue expandAt; fun_prop
lemma read_gauge (o : Site n) (p : Turn b) (f : Site n→G.El) : registered b (Lattice.gauge f U) o p=f o * registered b U o p * (f o)⁻¹ := by
  unfold registered used central; rw [expandAt_gauge,Lattice.face_gauge,Lattice.face_gauge,Lattice.face_gauge]
  simp only [leaves,travel_gauge,stops, map_zero,zero_add]; group

-- Fix word once, not depending on v.
def word (G : Gauge) {o : Site n} {b : ℕ} (h : 2*(b+1)<n.val) (x : Dim o b) := Classical.choose (rolled G _ _ (register h x).property.1 (register h x).property.2)
lemma lengths_word (G : Gauge) {o : Site n} {b : ℕ} (h : 2*(b+1)<n.val) (x : Dim o b) : (word G h x).length ≤ 4*b :=
    le_trans (Classical.choose_spec (rolled G _ _ (register h x).property.1 (register h x).property.2)).1 (bounded (register h x).property.1)
lemma spun (U : Config G n) (o : Site n) {b : ℕ} (h : 2*(b+1)<n.val) (x : Dim o b) : spine U o x.val=played (registered b U o) (word G h x) := by
  rw [heart _ U h o]
  exact (Classical.choose_spec (rolled G _ _ (register h x).property.1 (register h x).property.2)).2 _

-- Test links restricted: transported & nonwrapping.
variable {U b}
lemma content {o : Site n} (h : 2*(b+1)<n.val) (H : Hol G) (J : Labels.Jet G) (d) (x : ℝ) :
    Agrees (box b) (expandAt o (H.testLinks d o J x)) (H.links d J x) := by
  rintro ⟨k,i⟩ he ht; unfold expandAt Hol.testLinks; dsimp only; rw [add_sub_cancel_right,borne h _ he]
lemma feeling (H : Hol G) (J : Labels.Jet G) (d x) (o : Site n) (h : 2*(b+1)<n.val) (i : Dim o b) :
    spine (H.testLinks d o J x) o i.val= central (H.links d J x) (register h i).val := by
  rw [heart]; unfold central
  let V:= H.testLinks d o J x; let W:= expandAt o V
  have hx (z : Cover) (he : z ∈ box b) : leaves W z=leaves (H.links d J x) z := by
    apply travel_local _ _ _ _; intro i hi hk; exact content h H J d x _ (village _ he _ hi) (village _ he _ hk)
  let a:= register h i
  change leaves W a.val.1* W a.val*(leaves W (a.val.1+step a.val.2))⁻¹=_; rw [hx _ a.property.1,hx _ a.property.2,show W a.val=H.links d J x a.val from content h H J d x _ a.property.1 a.property.2];rfl
end YM.Next.Rank.Spindle

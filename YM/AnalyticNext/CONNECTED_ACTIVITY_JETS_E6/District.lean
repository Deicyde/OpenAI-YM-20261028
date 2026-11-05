import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sections

/-!
# Allocation of H sets: no double use

Require all visits including neighbors at interface, no checking only a
point frame/signed center. Use domain ℱ on the compulsory entries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Layout
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Packets Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A : Stores S} {l B d : ℕ} {Y : Finset (Stores S)}
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {U : Stores S→Finset ι}

structure Split (Y : Finset (Stores S)) (Q : Finset ι) (P : Stores S→Finset ι) : Prop where
  union : Y.biUnion P=Q
  split : (Y:Set (Stores S)).PairwiseDisjoint P

lemma Split.price_prod {Q : Finset ι} (h : Split Y Q U) (f : ι→ℝ) :
    (∏ i∈Q,f i)=∏ A∈Y,∏ i∈U A, f i := by rw [← h.union, Finset.prod_biUnion h.split]
lemma Split.price_sum {Q : Finset ι} (h : Split Y Q U) (f : ι→ℝ) :
    (∑ i∈Q,f i)=∑ A∈Y,∑ i∈U A, f i := by rw [← h.union, Finset.sum_biUnion h.split]
lemma Split.filtered {Q : Finset ι} (h : Split Y Q U) (p : ι→Prop) [DecidablePred p] :
    Split Y (Q.filter p) (fun i => (U i).filter p) := by
  refine ⟨by rw [← Finset.filter_biUnion,h.union],fun i hi j hj ht => (h.split hi hj ht).mono (filter_subset ..) (filter_subset ..)⟩

lemma sectors (H : Layout A l B Y) (he : d ≤ l*B) : Split Y (A.dome d) (fun i => i.dome d) := by
  refine ⟨H.field d,fun i hi j hj hn=> ?_⟩; exact (H.crews hi hj hn).mono (Corona.halo_mono he (by rfl))
    (Corona.halo_mono he (by rfl))

lemma readLines [Fintype ι] (H : Layout A l B Y) (W : Support c → Finset ι) (r : ι → Support c)
    (hw : ∀ X i, i∈W X ↔ ¬Disjoint X (r i)) (hp : ∀ i, ∀ x∈r i,∀ y∈r i, separation x y+d≤l*B) :
    Split Y (W (A.dome d)) (fun i => W (i.dome d)) := by
  constructor
  · ext i; rw [hw,← H.field d]; simp_rw [Finset.mem_biUnion,hw,Finset.not_disjoint_iff]; constructor
    · rintro ⟨b,hb,x,hx,h⟩; exact ⟨x,mem_biUnion.mpr ⟨b,hb,hx⟩,h⟩
    rintro ⟨x,hx,h⟩; obtain ⟨b,hb,hx⟩ := mem_biUnion.mp hx; exact ⟨b,hb,x,hx,h⟩
  intro b hb c hc ht; apply Finset.disjoint_left.mpr; intro i hi hj
  obtain ⟨x,hx,HX⟩ := Finset.not_disjoint_iff.mp ((hw _ _).mp hi)
  obtain ⟨y,hy,HY⟩ := Finset.not_disjoint_iff.mp ((hw _ _).mp hj)
  have hg : y ∈ b.dome (l*B) := touch_extend hx (by rw [Nat.add_comm]; exact hp i x HX y HY)
  exact Finset.disjoint_left.mp (H.crews hb hc ht) hg (Corona.halo_mono (le_trans (Nat.le_add_left _ _) (hp i x HX y HY))
    (Finset.Subset.refl _) hy)

lemma readPoints [Fintype ι] (H : Layout A l B Y) (X : Stores S → Finset ι) (f : ι→ Site c)
    (he : d ≤ l*B) (h : ∀ b i,i∈ X b ↔ f i∈ b.dome d) : Split Y (X A) X := by
  have hs : X=fun b => (univ.filter fun i:ι => f i∈ b.dome d) := by funext b; ext i; simp [h]
  rw [hs]; exact H.readLines (fun W => univ.filter (fun i:ι => f i∈W)) (singleton ∘ f)
    (by simp) (by
      intro i x hx y hy; rw [show x=f i from mem_singleton.mp hx,show y=f i from mem_singleton.mp hy,separation_self,zero_add]; exact he)

lemma streamed (H : Layout A l B Y) (d) (he : d ≤ l*B) (s : Signed) :
    Split Y (posted (turnStore s A) d) (fun i=>posted (turnStore s i) d) := H.readPoints _ (fun i => s.act (lead S i)) he
      fun _ _ => Census.posted_here ..

lemma subFine (H : Layout A l B Y) (d) (he : d ≤ l*B) : Split Y (vias S A d) (fun i => vias S i d) := by
  exact H.readPoints (fun i =>vias S i d) S.ratio.parent he fun b i=> by simp [vias,Inside]

lemma subFace (H : Layout A l B Y) (d) (hp : 2+d ≤ l*B) :
    Split Y (Mask.readFine (A.dome d) S) (fun i => Mask.readFine (i.dome d) S) := by
  refine H.readLines (fun W => Mask.readFine W S) (startPos S) (by simp [readFine]) ?_
  intro i x hx y hy
  let p : Seed S := .inl i
  have he := separation_triangle x (Packets.anchor S p) y
  exact ((Nat.add_le_add_right (he.trans (le_trans (Nat.add_le_add ((separation_comm ..).trans_le (price_one S p x hx))
    (price_one S p y hy)) (by rfl))) _).trans hp)

lemma subPin (H : Layout A l B Y) (d) (hp : 2+d≤l*B) :
    Split Y (readBonds (A.dome d)) (fun i=>readBonds (i.dome d)) := by
  refine H.readLines readBonds pinPos (by simp [readBonds]) ?_
  intro i x hx y hy
  let p : Seed S := .inr (.inl i)
  have he := separation_triangle x (Packets.anchor S p) y
  exact (Nat.add_le_add_right (he.trans (le_trans (Nat.add_le_add ((separation_comm ..).trans_le (price_one S p x hx))
    (price_one S p y hy)) (by rfl))) _).trans hp

lemma wraps (H : Layout A l B Y) (d) (he : 2+d ≤ l*B) :
    Split Y (visit A d) (fun i => visit i d) := by
  simp_rw [show ∀ A:Stores S,visit A d=univ.filter (fun i=> ¬Disjoint (A.dome d) (ends S i)) from fun _ => by ext; simp only [visit,mem_filter, voyage]]
  refine H.readLines (d:=d) (fun W => univ.filter (fun i => ¬Disjoint W (ends S i))) (ends S)
    (by simp) ?_
  intro i x hx y hy
  have ht := (separation_triangle x (atEdge S i) y).trans
    (add_le_add (stride i hx) ((separation_comm ..).trans_le (stride i hy)))
  exact (Nat.add_le_add_right ht _).trans he

lemma plaza_sub (H : Layout A l B Y) (d) (he : 2+d ≤ l*B) (X : Coat T F) :
    Split Y (X.plaza (A.dome d)) (fun i => X.plaza (i.dome d)) := by
  have hs (A : Stores S) : X.plaza (A.dome d)=(visit A d).filter (fun i=> X.Hot i) := by ext i; simp [visit,voyage,plaza,and_comm]
  simp_rw [hs]; exact (wraps H d he).filtered _
end YM.ConnectedActivityE6.Layout

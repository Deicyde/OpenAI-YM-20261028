import YM.RemainderComparison.WickReps.Quarry
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Creek
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι β : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet Serif Typeface
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "P₀"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)(Z:Set ι)(δ:ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l δ H τ K Y I)
local notation "Lt"=> sits Z l δ
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable [DecidableEq β]{Jm:Marker.Census β}
variable (z:ι→Marker.Poly Jm) {gP:β→ℝ} (hZ : Chorus Jm gP Z z k)
open Mallow Ovens Progress.DirectedRecipe
open WickReps
local notation "Tt"=> Sleet.Staff Vx H
local notation "Σ₁" => Mosaic.etude Vx H χ
local notation "Σ₂" => Mosaic.etude Vy H χ
open Mosaic Serif
def theater : Manor G c ι α (Staff (brand M x') H) :=
    ⟨fun i=>Beam.dashboard H i.fst,fun u i => (etude (brand M u) H χ i.fst i.snd|>.emit Lt),
       fun i=>(etude Vx H χ i.fst i.snd).letters,fun _=>False⟩
local notation "A₀" => theater H χ M x' l Z δ
local notation "Rt" => Flues.candle M x' S
variable (P':BudgetPoint)
lemma point (i:Tt): (A₀).halls i=Sleet.Base Vx H i:= Solo.locus H _
lemma paper (i:Tt) : (A₀).marks i=(etude Vy H χ i.fst i.snd).letters:=rfl
lemma leaves (i:Tt)(j:ι): j∈ (A₀).marks i ↔ j∈ page Vx H i.fst i.snd:=
   (Mosaic.holds univ (fun j=> (tile Vx H χ (i.fst.snd j).val (i.snd j)).letters) j).trans (Finset.mem_biUnion.symm)

lemma symmetry {i:Tt}(he : ∀ x,P'.Regular (Sleet.Base Vx H i) ( (A₀).solvent x i)):
       Manor.Sees A₀ P' Rt i:=by
   rw [← point H χ M x' l Z δ i] at he; refine ⟨he,?_,fun _ h=>False.elim h⟩
   intro y j hj U hv; rw [point]
   apply (Lyric.grown (brand M y) H χ i.1 i.2 U ?_).2.2 j ((leaves H χ M x' l Z δ i j).mp hj)
   intro hg; apply hv; unfold Manor.wet; rw [if_neg (show ¬ (A₀).total i from id)]
   by_cases hp: Healthy P'.threshold ((A₀).halls i) U
   · rw [masked_eq _ _ _ _ hp]; change _ * string _ _ _ _ _ U=0; rw [hg,mul_zero]
   exact masked_ne _ _ _ _ hp

lemma stony (i:Tt) (V : Config G c) (hx:P'.threshold=Pressure.temp x) : (A₀).paint P' Z z y V i=glyph (brand M y) H χ Z l δ z i V:=by
   unfold Manor.paint Serif.glyph Verse.paint; refine congr_arg₂ (· • ·) ?_ rfl
   refine congr_arg Complex.ofReal ?_; unfold Manor.wet; rw [if_neg (show ¬ (A₀).total i from id), point,hx]; unfold Verse.emit
   by_cases hp:Healthy (Pressure.temp x) (Sleet.Base Vx H i) V
   · unfold Mosaic.jewel; dsimp only; unfold Lyric.cut; rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp]; rfl
   unfold Mosaic.jewel; dsimp only; unfold Lyric.cut; rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,mul_zero]

-- Chlor Academy
open Verse
lemma blasted (p:Multiset ι)(h:¬ ((p.filter (fun i=>i∈Z)).Nodup)) : (∀ i,z i*z i=0)→ Verse.controls Z z p=0:=by
   intro ht; induction p using Multiset.induction_on with
   | empty=> simp at h
   | cons i p hi=>
      unfold Verse.controls; rw [Multiset.map_cons,Multiset.prod_cons]; split
      next hv=>
        by_cases he:i∈p
        · obtain ⟨p,rfl⟩:= Multiset.exists_cons_of_mem he
          rw [Multiset.map_cons,if_pos hv,Multiset.prod_cons,←mul_assoc,ht,zero_mul]
        exact mul_eq_zero_of_right _ (hi (fun hp=>h (by simp [he,hv,hp])))
      next hv=>rw [one_mul]; exact hi (fun hp=>h (by simp [hv,hp]))

-- Adopt alphabet under *all* tests given Chorus. root obligations remain.
def Academy (k:ℕ) : Set Tt := {i| load Z ( (A₀).marks i) ≤ k ∧ (( (A₀).marks i).filter (fun j=>j∈Z)).Nodup}
local notation "Ac₀"=> Academy H χ M x' l Z δ k
include hZ
lemma onCampus (i:Tt) (V:Config G c)(he:i ∉ Ac₀) : Manor.paint A₀ P' Z z y V i=0 :=by
   unfold Manor.paint; by_cases ht: Verse.load Z ((A₀).marks i)≤ k
   · rw [blasted Z z _ (fun h=> he ⟨ht,h⟩) hZ.square,smul_zero]
   rw [hZ.capacity _ (lt_of_not_ge ht), smul_zero]
omit hZ
lemma issued (i:Tt): ((A₀).marks i).toFinset = page Vx H i.fst i.snd :=by ext j; rw [Multiset.mem_toFinset,leaves]
lemma rounds (i:Tt): ((A₀).marks i).Nodup ↔ Turns Vx H i.fst i.snd:=by
   rw [← Multiset.toFinset_card_eq_card_iff_nodup, issued H χ M x' l Z δ, show ((A₀).marks i).card=_ from Muse.scores Vx H χ i.1 i.2, ← Lyric.octave]; unfold Lyric.after
   have h : (page Vx H i.1 i.2).card ≤ Lyric.notes Vx H i.1 i.2:= Finset.card_biUnion_le; omega
lemma accord {z:Tt}(hv:Muse.virgin Vx H χ Z z.1 z.2): ( ((A₀).marks z).filter (fun x=>x∈Z))=(A₀).marks z:=by
   have he:( ((A₀).marks z).filter (fun x=>x∈Zᶜ))=0:= Multiset.card_eq_zero.mp (by unfold Muse.virgin Verse.load at hv; convert hv using 2; congr)
   apply Multiset.filter_eq_self.mpr; intro i hi; by_contra hp; have hv : i∈ ( ((A₀).marks z).filter (fun x=>x∈Zᶜ)):=Multiset.mem_filter.mpr ⟨hi,hp⟩; rw [he] at hv; exact Multiset.notMem_zero i hv

lemma choir {z:Tt} (hW:z∈Ac₀) (hv:Muse.virgin Vx H χ Z z.1 z.2) : Turns Vx H z.1 z.2∧ (A₀).marks z= (page Vx H z.1 z.2).val:=by
   have ht:( (A₀).marks z).Nodup:= accord H χ M x' l Z δ hv ▸ hW.2
   rw [← issued H χ M x' l Z δ,Multiset.toFinset_val,Multiset.dedup_eq_self.mpr ht]; exact ⟨(rounds H χ M x' l Z δ z).1 ht,rfl⟩ -- expression adapt
end YM.RemainderComparison.Creek

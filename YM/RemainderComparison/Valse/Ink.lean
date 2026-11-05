import YM.RemainderComparison.Valse.Notes
import YM.RemainderComparison.Lobby.Doses
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Valse
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open PhysicalNext.Repeat Lotus Merge Palette Turn
open Mosaic
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {ι ι' δ : Type} {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}
    {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    {W α μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {L : Side}
    {R : Rep G f} (H : Cash W α μ L Q o C T R)
open Match Sleet Mosaic Blaze March Captain Typeface Lyric Lotus
variable {α' : Type*}(M:ι→Portrait R α')(a b' : α')(χ: Chi) (u: Set ι)
-- fights. Complement embedding.

def start : (↑(uᶜ)) ↪ ι:=⟨Subtype.val,Subtype.val_injective⟩
local notation "N₁" => start u
local notation "Xv" => Typeface.brand M a
local notation "Yv" => Typeface.brand M b'

lemma stands (p : Multiset ι) : (∀ i∈p,i ∈ uᶜ) ↔ Verse.load u p=0:=by
    unfold Verse.load; rw [Multiset.card_eq_zero]; refine ⟨fun h=>?_,fun h i hi hp=>?_⟩
    · induction p using Multiset.induction_on with
      | empty=>simp
      | cons i p ih => rw [Multiset.filter_cons_of_neg _ (h i (Multiset.mem_cons_self ..))]; exact ih fun j hj=>h _ (Multiset.mem_cons_of_mem hj)
    exact Multiset.notMem_zero i (h ▸ Multiset.mem_filter.mpr ⟨hi,hp⟩)

section general
variable (Xp:ι→Leaf R)(p:Staff Xp H)
local notation "Yp"=> Xp ∘ N₁
local notation "B₀" => etude Xp H χ
lemma covers (w:Drums Xp S) : w∈Set.range (Script.drums Xp N₁ S)↔ ∀ i∈w.val, i∈uᶜ :=by
    constructor
    · rintro ⟨j,rfl⟩ i hi
      obtain ⟨k,hk,rfl⟩:=mem_map.mp hi; exact k.property
    intro h; let r:= w.val.preimage N₁ ((N₁).injective.injOn) -- weird ↑u.is notation
    let w':Drums (Xp ∘ N₁) S:= ⟨r,fun i hi j hj eq=> (N₁).injective (w.prop (Finset.mem_preimage.mp hi) (Finset.mem_preimage.mp hj) eq)⟩
    refine ⟨w',Subtype.ext ?_⟩; ext i; constructor
    · intro hi; obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hi; exact Finset.mem_preimage.mp (show j∈r from hj)
    intro hi; let x: ↑(uᶜ):= ⟨i,h i hi⟩; exact mem_map.mpr ⟨x,(show x∈r from mem_preimage.mpr hi),rfl⟩
lemma career' (p:H.fragrances)(i: Syllable Xp H p): i∈ Set.range (Script.label Xp H (N₁) p) ↔ Verse.load u ((B₀ p i).letters)=0:= by
   have hp : (∀ j, i j∈Set.range (Script.drums Xp (N₁) S)) ↔ Verse.load u ((B₀ p i).letters)=0:=by
      rw [← stands]; simp_rw [covers u]; unfold etude; dsimp only; simp_rw [Mosaic.holds]
      constructor
      · rintro h i' ⟨j,hj,hi⟩; exact h j i' hi
      intro h j i' hi; exact h i' ⟨j,mem_univ _,hi⟩
   constructor
   · rintro ⟨i,rfl⟩; exact hp.mp fun j=> ⟨i j,rfl⟩
   intro h; choose s hs using hp.mpr h; exact ⟨s,funext fun j=> hs j⟩

lemma podium (p:H.Chapter)(i:Stone Xp H p): i∈ Set.range (Script.board Xp H (N₁) p) ↔ Verse.load u ((Mosaic.panel Xp H χ p i).letters)=0:=by
   rcases p with p|p; exact (covers u Xp i).trans (stands u _)
   exact career' H χ u Xp p i
lemma gathering (p:H.Chainbook)(i:Scene Xp H p): i∈ Set.range (Script.queue Xp H (N₁) p) ↔ Verse.load u ((Mosaic.parade Xp H χ p i).letters)=0:=by
   have hv : (∀ j k, i j k ∈ Set.range (Script.board Xp H (N₁) j.val))↔ Verse.load u ((Mosaic.parade Xp H χ p i).letters)=0:=by
      simp_rw [podium H χ,← stands]; constructor
      · intro h j hj; obtain ⟨i',hi,hx⟩:= (holds univ (fun k:↥p.fst=>∑ j,(panel Xp H χ k.val (i k j)).letters) j).1 hj
        obtain ⟨v,v',hk⟩:= (holds univ (fun j =>(panel Xp H χ i'.val (i i' j)).letters) j).1 hx; exact h i' v _ hk
      intro h j k x hx; refine h x ((holds univ (fun j:↥p.fst=> ∑ k, (panel Xp H χ j.val (i j k)).letters) x).mpr ⟨j,mem_univ _,?_⟩); exact (holds univ (fun k=> (panel Xp H χ j.val (i j k)).letters) x).mpr ⟨k,mem_univ k,hx⟩
   constructor; · rintro ⟨i,rfl⟩; exact hv.1 fun j k=>⟨i j k,rfl⟩
   intro h; choose v hv' using hv.2 h; exact ⟨v,funext fun i=>funext fun j=> hv' i j⟩
end general

variable (v : ℝ)(l:ι→ ℝ)
local notation "S₀"=> Lobby.night (Creek.theater H χ M a l u v) u
local notation "P₁"=> Xv ∘ (start u)
local notation "Pʼ"=> P₁

def stage : Sleet.Staff P₁ H ↪ Staff Xv H:= Embedding.sigmaMap (Embedding.refl _) (fun p=> Script.label Xv H (N₁) p)
local notation "Ω₁"=> stage H M a u
lemma from_alley (i:Staff Xv H): i∈ S₀↔ i ∈ Set.range (stage H M a u):=by
   obtain ⟨p,i⟩:=i; constructor
   · intro h; obtain ⟨x,hx⟩:= (career' H χ u Xv p i).2 h; rw [← hx]; exact ⟨⟨p,x⟩,rfl⟩
   rintro ⟨⟨s,k⟩,h⟩; rw [← h]; exact (career' H χ u Xv s (Script.label Xv H N₁ s k)).1 ⟨k,rfl⟩
lemma lights (i:Staff P₁ H) (k:ℕ) : (Ω₁ i) ∈ Creek.Academy H χ M a l u v k:=by
    let s:= (Creek.theater H χ M a l u v).marks (Ω₁ i); let g:= (s.filter (fun j=> j∈u)); have hv:g.card=0:= ((from_alley H M a χ u v l _).mpr ⟨_,rfl⟩)
    exact ⟨hv.trans_le (Nat.zero_le _),show g.Nodup from (by rw [Multiset.card_eq_zero.mp hv]; exact Multiset.nodup_zero)⟩

end YM.RemainderComparison.Valse

import YM.MergeProof.Badlands
import YM.FullVolume.Fields.Flight
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom Accent Menu Motion Extra.Multi Next.Rank Next.Rank.Spindle
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
variable (C:Family G) (d : V → ℕ)(N k p:ℕ)
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "B!"=> C.path.rep N p
variable (W: Bid.Worth) (u ψ φ δ: ℕ→ℝ)(ζ:ℕ→ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
variable (s:(i:V)→ C.label (d i)) (f:∀ m:ℕ,V→ Site (C.side m p)) (g:V→Motion)(purse: V→ℝ)
   {q:∀ m:ℕ,m≤N→ Config G (C.side m p)→Poly B} -- fix notation
local notation "Z"=> (fun i=> item C (d i) N p (s i) (fun j=>f j i) (g i))
local notation "k!"=> (fun m i=> Ktone C (d i) N p (s i) (fun j=> f j i) (g i) m)
local notation "f!"=> (fun m i=> indexX C (d i) N p (s i) (fun j=> f j i) (g i) m)
structure Ponds (p k N :ℕ) : Prop where
   night : Retain C.path r δ u D N p k
   cost : roomCost C.path.levels W
   back : Bank W C.path.levels
   stay : Brine C.path k δ φ
   mom : Monotone r
   stocks (j:ℕ)(he:C.ref j ≤ k) (hk:k≤N): Freightage C W ψ D j N p ∧ ∃ X, Fiesta C.path (C.labels.level j) (ζ j) ψ k ∧ Cherry j k C.path φ (ζ j) ∧ Banks C.path (C.labels.level j) X u (ζ j) N ∧ coverNumber (C.path.levels.budget N).B ((C.localSection j).footprint (0:Site (C.side N p))) ≤ 1 ∧ (∀ (i:(C.labels.level j).Index)(U:Config G (C.side N p)), ‖(C.localSection j).places (Size.axis (C.labels.level j) i) 0 U‖ ≤ X)
lemma Geyser.pond (hh:Geyser C W u ψ φ δ ζ r D):Ponds C W u ψ φ δ ζ r D p k N:=by
    have hf:Brine C.path k δ φ:=⟨fun i _=> hh.stay.water _ (Nat.zero_le i),fun i _=> hh.stay.mint _ (Nat.zero_le i),fun i _=> hh.stay.split _ (Nat.zero_le i),fun i _=> hh.stay.support _ (Nat.zero_le i)⟩
    exact ⟨allRetain C.path r δ u D hh.night p N k,hh.cost,hh.back,hf,hh.mom,fun i hi he=>⟨hh.aim i N p (hi.trans he), hh.heights i k N p hi he⟩⟩
lemma Ponds.past (hh : Ponds C W u ψ φ δ ζ r D p k N)(h:C.path.Selected)(hs:∀ i,(C.localSection (d i)).Sound C.params)(he:∀ i,C.ref (d i) ≤ k)(hk:k≤N)(hm:Occupancy (f k) (r k))(hx:Migrating C.path k p N f)(hz:Drake B (P k).B (f k))
    (hM:∀ i,purse i*paid C (d i) k N p (s i) ≤ ζ (d i) k)(hw:∀ i,0<purse i) : ∃ g': ∀ m:ℕ,V→ℕ→ Config G (C.side m p)→ℂ,(∀ j:V, Nectar C.path u D p N k f (march purse φ k) f! g' Z j)∧ ∀ i,k ≤ i→ i≤N→ tapes C.path p N g' i=k! i:=by
    have hf:=hh.stay
    let w:= march purse φ k
    let θ:= f!
    let Ω:= k!
    have hx':= desal C.path r k p N δ φ f purse hw hf B hx hz hh.mom hm
    have hW:=marines k φ purse hw
    have hb(j:V) : ∃ g':∀ m:ℕ,ℕ → Config G (C.S.side m p)→ℂ, Wild C.path u k N p (fun m=>f m j) (fun m=>w m j) (fun m=>θ m j) g' (Z j) D ∧ ∀ i,k ≤ i→ i≤N→ profile (B! i).activities (g' i)=Ω i j := by
        obtain ⟨M,hI,hS,hK,hY⟩:= ((hh.stocks (d j) (he j) hk).1).lyrics
        obtain ⟨v,hF,hX,hB,hb,hH⟩:= (hh.stocks (d j) (he j) hk).2
        let Y:= (C.factory (d j) N p).terminal.symm (s j)
        have hp(m):parcel C (d j) m N p (s j)=(M.tone m).plays Y:=by unfold parcel; rw [hI];rfl
        have hZ: Sung (C.localSection (d j)) H N p C.params W k M:= ⟨hS.head,hk,fun j' hi=> hS.earned _ ((he j).trans hi),fun j' hi=> hS.step _ ((he j).trans hi)⟩
        have hM': purse j*bond H N p M k Y ≤ ζ (d j) k:=by
           refine le_trans (le_of_eq (congr_arg (purse j* ·) ?_)) (hM j)
           unfold Next.Rank.Spindle.paid Price.awake Price.columns -- inspect
           rw [Size.smul]; unfold bond; congr 1;rw [← (hS.earned k (he j) hk).currents Y] -- hint
           exact congr_arg (C.labels.level (d j)).coeffSize (congr_arg Coefficient.x (hp k).symm)
        let w' m:=w m j; have hu(i)(hc:k ≤ i)(hp:i≤N):0 < w' i:= hx'.pos _ hc hp j
        have h'(m)(hi:k ≤ m): w' (m+1)=φ m*w' m:= by unfold w' w; simp only [march,if_pos hi]
        simp_rw [θ,Ω,indexX,Ktone,hp]
        apply sweet C.path C.params (C.localSection (d j)) W (ζ (d j)) u ψ v k N p M Y (g j) (fun m=>f m j) w' D h (hs j) hZ hu ?_ ?_ hF hB hb hH ?_ (hY _) ?_
        · intro i h hp; rw [h' i h]; exact mul_le_of_le_one_left (hu i h hp.le|>.le) (hX.level i h)
        · apply cost_chain C.path C.params (C.localSection (d j)) W (ζ (d j)) k N p M Y w' le_rfl (fun i h hp=> (hu i h hp).le) hk (fun i h hi=>?_) (fun i h hp=> hu i h hp.le) hh.cost hh.back hZ
          · simpa only [w',w,hW] using! hM'
          rw [h' i h]; exact le_trans (le_of_eq (b:=φ i* (((C.S.block i).val:ℝ)^(d j) * (C.path.levels.params (i+1)).columns)*ζ (d j) i*w' i) (by ring)) (mul_le_mul_of_nonneg_right (hX.cost i h) ((hu i h hi.le).le))
        · intro i hy hm; exact congr_fun (hx.mare i hy hm).symm j
        intro i hi hp; obtain ⟨y,w,hp',-⟩:= hh.night.days i hi hp; exact ⟨hK i ((he j).trans hi) hp,hp'.propagate⟩
    choose g' hg hU using hb
    let G' i (j:V):= g' j i
    have hν(j:V):Nectar C.path u D p N k f w θ G' Z j:=by
       obtain ⟨h1,h2,h3,h4,h5⟩:=hg j; exact ⟨h1,h2,h3,h4,h5⟩
    exact ⟨G',hν,fun i hi hx=>funext fun j=> hU j i hi hx⟩
end YM.MergeProof
#print axioms YM.MergeProof.Ponds.past

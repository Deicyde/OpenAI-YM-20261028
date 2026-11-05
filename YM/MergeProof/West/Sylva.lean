import YM.MergeProof.Badlands
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
lemma Geyser.sylvan (hh : Geyser C W u ψ φ δ ζ r D)(h:C.Makes)(he:∀ i,C.ref (d i) ≤ k)(hk:k≤N)(hm:Occupancy (f k) (r k))(hx:Migrating C.path k p N f)(hz:Drake B (P k).B (f k))
    (hM:∀ i,purse i*paid C (d i) k N p (s i) ≤ ζ (d i) k)(hw:∀ i,0<purse i)(ht:∀ i:ℕ,k ≤ i →∀ hi:i<N,q i hi.le=(C.path.levels.clock.op i p).push ((C.path.rep N p (i+1)).beta) (q (i+1) hi))
    (hv:q N le_rfl=birth B (C.path.rep N p N) Z) (hP: Integrable (q N le_rfl) (prior G (C.side N p))) : ∀ i:ℕ,k ≤ i→∀ hN:i≤N, Served (B! i) (f! i) (k! i) (q i hN) (f i) (march purse φ k i) (topPitch C.path N i) 1:=by
    have hf:Brine C.path k δ φ:=⟨fun i _=> hh.stay.water _ (Nat.zero_le i),fun i _=> hh.stay.mint _ (Nat.zero_le i),fun i _=> hh.stay.split _ (Nat.zero_le i),fun i _=> hh.stay.support _ (Nat.zero_le i)⟩
    let w:= march purse φ k
    let θ:= f!
    let Ω:= k!
    have hx':= desal C.path r k p N δ φ f purse hw hf B hx hz hh.mom hm
    have hW:=marines k φ purse hw
    have hb(j:V) : ∃ g':∀ m:ℕ,ℕ → Config G (C.S.side m p)→ℂ, Wild C.path u k N p (fun m=>f m j) (fun m=>w m j) (fun m=>θ m j) g' (Z j) D ∧ ∀ i,k ≤ i→ i≤N→ profile (B! i).activities (g' i)=Ω i j := by
        obtain ⟨M,hI,hS,hK,hY⟩:= (hh.aim (d j) N p ((he j).trans hk)).lyrics
        obtain ⟨v,hF,hX,hB,hb,hH⟩:= hh.heights (d j) k N p (he j) hk
        let Y:= (C.factory (d j) N p).terminal.symm (s j)
        have hp(m):parcel C (d j) m N p (s j)=(M.tone m).plays Y:=by unfold parcel; rw [hI];rfl
        have hZ: Sung (C.localSection (d j)) H N p C.params W k M:= ⟨hS.head,hk,fun j' hi=> hS.earned _ ((he j).trans hi),fun j' hi=> hS.step _ ((he j).trans hi)⟩
        have hM': purse j*bond H N p M k Y ≤ ζ (d j) k:=by
           refine le_trans (le_of_eq (congr_arg (purse j* ·) ?_)) (hM j)
           unfold Next.Rank.Spindle.paid Price.awake Price.columns -- inspect
           rw [Size.smul]; unfold bond; congr 1;rw [← (hS.earned k (he j) hk).currents Y] -- hint
           exact congr_arg (C.labels.level (d j)).coeffSize (congr_arg Coefficient.x (hp k).symm) -- maybe simplify
        let w' m:=w m j; have hu(i)(hc:k ≤ i)(hp:i≤N):0 < w' i:= hx'.pos _ hc hp j
        have h'(m)(hi:k ≤ m): w' (m+1)=φ m*w' m:= by unfold w' w; simp only [march,if_pos hi]
        simp_rw [θ,Ω,indexX,Ktone,hp]
        apply sweet C.path C.params (C.localSection (d j)) W (ζ (d j)) u ψ v k N p M Y (g j) (fun m=>f m j) w' D h.wilson (h.sections (d j)) hZ hu ?_ ?_ hF hB hb hH ?_ (hY _) ?_
        · intro i h hp; rw [h' i h]; exact mul_le_of_le_one_left (hu i h hp.le|>.le) (hX.level i h)
        · apply cost_chain C.path C.params (C.localSection (d j)) W (ζ (d j)) k N p M Y w' le_rfl (fun i h hp=> (hu i h hp).le) hk (fun i h hi=>?_) (fun i h hp=> hu i h hp.le) hh.cost hh.back hZ
          · simpa only [w',w,hW] using! hM'
          rw [h' i h]; exact le_trans (le_of_eq (b:=φ i* (((C.S.block i).val:ℝ)^(d j) * (C.path.levels.params (i+1)).columns)*ζ (d j) i*w' i) (by ring)) (mul_le_mul_of_nonneg_right (hX.cost i h) ((hu i h hi.le).le))
        · intro i hy hm; exact congr_fun (hx.mare i hy hm).symm j
        intro i hi hp; obtain ⟨y,w,hp',-⟩:= hh.night.days N p i hp; exact ⟨hK i ((he j).trans hi) hp,hp'.propagate⟩
    choose g' hg hU using hb
    let G' i (j:V):= g' j i
    have hν(j:V):Nectar C.path u D p N k f w θ G' Z j:=by
       obtain ⟨h1,h2,h3,h4,h5⟩:=hg j; exact ⟨h1,h2,h3,h4,h5⟩
    intro i hi ha
    have ht':= Accent.sentry C.path r δ u D p N f w θ G' Z h.wilson hk hx' hh.night hν ht hv hP i hi ha|>.2.2
    have hq:tapes C.path p N G' i=Ω i:= funext fun j=> hU j i hi ha
    rw [hq] at ht'; exact ht' 
end YM.MergeProof

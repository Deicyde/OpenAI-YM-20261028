import YM.MergeProof.Badlands
import YM.MergeProof.North.Lichen
import YM.MergeProof.South.Window
import YM.Next.RANK.Compass


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom Accent Menu Motion Extra.Multi Next.Rank Next.Rank.Spindle Ribbon
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
section
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
variable (C:Family G) (d : Bool → ℕ)(N k p:ℕ)
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "B!"=> C.path.rep N p
variable (W: Bid.Worth) (u ψ φ δ: ℕ→ℝ)(ζ:ℕ→ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
variable (s:(i:Bool)→ C.label (d i)) (f:∀ m:ℕ,Name V→ Site (C.side m p)) (q:Bool→Motion)(a: Bool→ℝ) (v:V) (E:∀ m:ℕ,V→ Site (C.side m p)) (M:V→ Motion) (β:V→Equiv.Perm V)
   (F:Name V→ Config G (C.side N p)→ℂ)(σ χ:ℕ→ℝ)
local notation "κ"=> (Aged V)
local notation "t"=> (fun i=>MergeProof.item C (d i) N p (s i) (fun j=>f j (v,i)) (q i))
local notation "Λ"=> (fun j:Name V=>δ k * (φ k * a j.2))
lemma upper (hh : Geyser C W u ψ φ δ ζ r D)(h:C.Makes) {μ:ℕ} (hr:Thor C.path δ r D σ χ μ)(hp:μ≤k)(he:∀ i,C.ref (d i) ≤ k)(hk:k<N)(hm:Occupancy (f k) (r k))(hx:Migrating C.path k p N f)(hz:Drake κ (P k).B (f k)) (hM:∀ i,a i*paid C (d i) k N p (s i) ≤ ζ (d i) k) (hw:∀ i,0<a i)
     (hi:Migrating C.path k p N E)(hP:∀ j,j≠v→β j v=j)(hT:∀ m:ℕ, k ≤ m→m≤N→∀ i,i≠v→∀ j:Bool,f m (i,j)=affine (M i).1 (E m i) (f m (v,j))) (hV:∀ j,j≠v→∀ b:Bool,F (j,b)=stepUp (M j) (E N j) (F (v,b)))(hy:∀ i,F (v,i)=t i)
     (hX:Integrable (birth κ (B! N) F) (prior G _)) :∃ l: Name V→ℂ,∃ g: Name V→ Config G (C.side k p)→ℂ,∃ L':Name V→ℕ→ Config G (C.side k p)→ℂ, (∀ i,Λ i*‖l i‖≤1) ∧ (∀ i,i≠v→ ∀ j:Bool,l (i,j)=scalar (M i) (l (v,j))) ∧ Arc (B! k) g L' (gust C.path N p N (birth κ (B! N) F) k hk.le) v M (E k) β (f k) (Λ) ((P k).supportExponent+1/2) ((P k).supportExponent+1) 1 (χ k) (δ k) l :=by
    have hF:Brine C.path k δ φ:=⟨fun i _=> hh.stay.water _ (Nat.zero_le i),fun i _=> hh.stay.mint _ (Nat.zero_le i),fun i _=> hh.stay.split _ (Nat.zero_le i),fun i _=> hh.stay.support _ (Nat.zero_le i)⟩
    let w:= march a φ k; let W' (i)(j:Name V):= w i j.2
    have hΔ(i):(march (fun j:Name V=> a j.2) φ k i)=W' i:=by
      induction i with
      | zero=>rfl
      | succ i IH=> unfold W' w march; split
                    · rename_i he; funext j; change φ i*(march (fun j:Name V=> a j.2) φ k i _) =_; rw [IH]
                    exact rfl
    have h': Matchup C.path r δ p N k f W' κ:= (funext hΔ) ▸ (desal C.path r k p N δ φ f (fun j=> a j.2) (fun i=>hw _) hF κ hx hz hh.mom hm)
    have ht:w (k+1)=fun j=>φ k*a j:=by unfold w; rw [march,if_pos le_rfl,marines _ _ _ hw]
    suffices hK:∀ j:Bool,∃ U:∀ m:ℕ,Config G (C.side m p)→ℂ,∃ L:∀ m:ℕ,ℕ → Config G (C.side m p)→ℂ,Stately H u k N p (fun m=>f m (v,j)) (fun m=>w m j) U L (F (v,j)) D by
      have hY:= tidal C.path u δ r D E f M v w β F h.wilson hh.night h' hP hV σ χ hr hp hi (S:=gust C.path N p N (birth κ (B! N) F)) (fun i _ he=> gust_step C.path N p N _ he) (gust_base ..) (fun i _ hn=> gust_live C.path _ _ _ _ hX hn) hk hK hT; simp only [ht] at hY; exact hY
    intro j
    obtain ⟨T,hI,hS,hK,hY⟩:= (hh.aim (d j) N p ((he j).trans hk.le)).lyrics
    obtain ⟨b,hQ,hL,hB,hb,hH⟩:= hh.heights (d j) k N p (he j) hk.le
    let Y:= (C.factory (d j) N p).terminal.symm (s j)
    have hp(m):parcel C (d j) m N p (s j)=(T.tone m).plays Y:=by unfold parcel; rw [hI];rfl
    have hZ: Sung (C.localSection (d j)) H N p C.params W k T:= ⟨hS.head,hk.le,fun j' hi=> hS.earned _ ((he j).trans hi),fun j' hi=> hS.step _ ((he j).trans hi)⟩
    let i:Name V:= (v,j); have hu(m:ℕ)(he:k ≤ m)(hn:m≤N):0<W' m i:= h'.pos m he hn i
    have hM': W' k i*bond H N p T k Y ≤ ζ (d j) k:=by
       unfold W' w; rw [marines k φ a hw]; refine le_trans (le_of_eq (congr_arg (a i.snd* ·) ?_)) (hM j)
       unfold Next.Rank.Spindle.paid Price.awake Price.columns; rw [Size.smul]; unfold bond; congr 1;rw [← (hS.earned k (he j) hk.le).currents Y]; exact congr_arg (C.labels.level (d j)).coeffSize (congr_arg Coefficient.x (hp k).symm)
    have hU(m)(he:k ≤ m): w (m+1) j= φ m*w m j:=by unfold w; rw [march,if_pos he]
    rw [hy j]; have hf:= stater H C.params (C.localSection (d j)) W (ζ (d j)) u ψ b k N p T Y (q j) (fun m=>f m (v,j)) (fun m=>w m j) D h.wilson (h.sections (d j)) hZ hu ?_ ?_ hQ hB hb hH ?_ (hY _) ?_; obtain ⟨g,hg,_⟩:= hf
    exact ⟨_,g,hg⟩
    · intro i h hp; rw [hU i h]; exact mul_le_of_le_one_left (hu i h hp.le|>.le) (hL.level i h)
    · apply cost_chain H C.params (C.localSection (d j)) W (ζ (d j)) k N p T Y (fun m=>w m j) le_rfl (fun i h hp=> (hu i h hp).le) hk.le (fun i h hi=>?_) (fun i h hp=> hu i h hp.le) hh.cost hh.back hZ hM'
      rw [hU i h]; exact le_trans (le_of_eq (b:=φ i* (((C.S.block i).val:ℝ)^(d j) * (C.path.levels.params (i+1)).columns)*ζ (d j) i*w i j) (by ring)) (mul_le_mul_of_nonneg_right (hL.cost i h) ((hu i h hi.le).le))
    · intro i hy hm; exact congr_fun (hx.mare i hy hm).symm _
    intro i h hp; obtain ⟨hF,-⟩:= hr.moon N p i (by omega) hp; exact ⟨hK i ((he j).trans h) hp,hF.propagate⟩
end
end YM.MergeProof.Ribbons

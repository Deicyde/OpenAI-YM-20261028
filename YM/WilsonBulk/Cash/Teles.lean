import YM.WilsonBulk.Cash.Plumes

/-!
# Universally deploy touching kernels at step
No cost assertions other than all tori & cover width/strip proof utilities.
`Favorable` holds on weighted rows at same existential, pointwise MANY n:
use specifically since user must not assert length Price after height given for
consume unchanged interactions. Here `lullaby` only invoked for structural
use, independent of heights during iteration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
variable {α β X Y : Type} {p q θ σ a b : ℝ} {n k : ℕ} {P U : Text α (n+1)} {L c f : Side} {d : Duct (Market α) (Market β)}
-- sessions; existence needed for Phi correction exact ident
abbrev Lighthouse (H : Row α β) := ∃ σ, 0<σ ∧ ∃ C,0≤C ∧ H.strip σ C
abbrev Plaza (H : Legs (Row α β) n) := ∃ σ, 0<σ ∧ ∃ C,0 ≤ C ∧ ∀ i,(H i).strip σ C
lemma plaza {H : Legs (Row α β) n} (h : ∀ i,Lighthouse (H i)) : Plaza H := by
  suffices ∀ s : Finset (Fin n), ∃ σ, 0<σ ∧ ∃ C,0 ≤ C ∧ ∀ i∈s,(H i).strip σ C by simpa using this univ
  intro s; induction s using Finset.induction with
  | empty=> exact ⟨1,one_pos,0,le_rfl,fun i hi=> (notMem_empty _ hi).elim⟩
  | insert a s ha ih=>
    obtain ⟨w,hw,c,hc,f⟩:= ih; obtain ⟨x,hx,d,hd,g⟩:= h a
    refine ⟨min w x,lt_min hw hx,c+d,add_nonneg hc hd,fun i h=>?_⟩
    rcases mem_insert.mp h with rfl|h
    · exact strip_mono g (min_le_right ..) (by linarith)
    exact strip_mono (f i h) (min_le_left ..) (by linarith)
lemma beacon (H : Row α β) (h : Stamped H) : Lighthouse H:= ⟨1,one_pos,h 1 zero_le_one⟩

section pricing
variable {S : Legs (Duct (Market α) (Market β)) (n+1)} (e : Cover→Cover)
variable {K : Legs (Cross L α β) (n+1)} {H : Legs (Row α β) (n+1)}
abbrev Trails (K : Legs (Duct (Market α) (Market β)) (n+1)) := ∀ σ:ℝ,0<σ→ ∃ θ, 0<θ ∧ ∃ d, Geometry (lawn α) (lawn β) σ θ d ∧ ∃ p q, ∀ i,AuditLine (K i) d (n+1) p q
abbrev Foible (e : Cover→ Cover) (S : Legs (Duct (Market α) (Market β)) n) := ∀ i x y b,S i (roll (e b) _ x) (roll b _ y)= S i x y
lemma Public.lantern (h : Public P) (hh : Trails S) (hg : Foible e S) : Public (tele S P) := by
  obtain ⟨σ,x,hs,hx⟩:= h.money; obtain ⟨θ,he,g,hT,p,q,HH⟩:= hh _ hs
  exact ⟨tele_roll e hg h.style, ⟨θ,q*p^n*x,he,fare_const hT HH hx⟩⟩
lemma lantern_coupon (T : Legs (Duct (Co f α) (Co c β)) (n+1)) (h : Public P) (hh : Trails S) (hg : Foible e S)
    (he : ∀ i, GaugeLine (small f α) (small c β) (S i) (T i)) : coupon c _ (tele S P)=tele T (coupon f _ P) := by
  obtain ⟨σ,x,hs,hx⟩:= h.money; obtain ⟨θ,hy,g,hT,p,q,HH⟩:= hh _ hs
  exact (h.lantern e hh hg).orates_once c ((coupon_reads f h.style).tele hT HH hx hy.le he) (by omega)
-- for unbounded k
lemma lantern_sub (h : Trails S) (hp : Public P) (hu : Public U) : tele S (P-U)=tele S P-tele S U := by
  obtain ⟨p,A,x,hx⟩:= hp.money; obtain ⟨q,B,y,hy⟩:= hu.money; obtain ⟨θ,he,g,hT,p,q,hS⟩:= h (min p q) (lt_min x y)
  exact tele_sub hT hS (hx.mono (min_le_left ..) le_rfl) (hy.mono (min_le_right ..) le_rfl) he.le
lemma lantern_add (h : Trails S) (hp : Public P) (hu : Public U) : tele S (P+U)=tele S P+tele S U := by
  obtain ⟨p,A,x,hx⟩:= hp.money; obtain ⟨q,B,y,hy⟩:= hu.money; obtain ⟨θ,he,g,hT,p,q,hS⟩:= h (min p q) (lt_min x y)
  exact tele_plus hT hS (hx.mono (min_le_left ..) le_rfl) (hy.mono (min_le_right ..) le_rfl) he.le
variable [Fintype α] [Fintype β]
lemma pickSpan (L : Side) (h : 0<σ) (he : 0<θ) (i : ℕ) : ∃ a:ℝ,0 < a ∧ a / L.val ≤ θ ∧ a ≤ σ ∧ (i:ℝ)*a ≤ σ := by
  have hw : (0:ℝ) < L.val:= by positivity
  let a:=min (σ/(i+1)) (θ*L.val)
  have hp : 0 < a := lt_min (div_pos h (by positivity)) (mul_pos he hw); have hh : a*(i+1)≤σ:= (le_div_iff₀ (by positivity : (0:ℝ) < i + 1)).mp (min_le_left ..)
  refine ⟨a,hp,(div_le_iff₀ hw).mpr (min_le_right ..),?_,?_⟩
  · have hi:= Nat.cast_nonneg (α:=ℝ) i; nlinarith
  nlinarith
lemma installMeet (h : Plaza K) : Trails (install ∘ K) := by
  obtain ⟨σ,hs,M,hM,h⟩:= h; intro θ ht; obtain ⟨a,hh,he,hp,hv⟩:= pickSpan L hs ht (n+1)
  exact ⟨a,hh,_,delta_shape hh.le he,_,_,fun i=> install_audited (h i) hM hh.le hp hv⟩
lemma plainMeet (h : Plaza H) : Trails (plain ∘ H) := by
  obtain ⟨σ,hs,M,hM,h⟩:= h; intro θ ht; obtain ⟨a,hh,he,hp,hv⟩:= pickSpan 1 hs ht (n+1)
  exact ⟨a,hh,_,delta_shape hh.le he,_,_,fun i=> plain_audited hh.le (h i) hM hp hv⟩
omit [Fintype α] [Fintype β]
section
lemma Foible.plain (H : Legs (Row α β) n) : Foible id (Pert.Bulk.plain ∘ H) := fun _ _ _ _=> plain_reads ..
lemma Foible.install (K : Legs (Cross L α β) n) : Foible (fun b=> L.val • b) (Pert.Bulk.install ∘ K) := fun _ _ _ _=> install_roll ..
end
end pricing
section bus
variable [Fintype α] [Fintype β] (g : Ratio c f)
lemma Public.ascend (h : Public P) {H : Legs (Row α β) (n+1)} (he : Plaza H) : Public (tele (plain ∘ H) P) := h.lantern id (plainMeet he) (Foible.plain H)
lemma Public.orient (h : Public P) {K : Legs (Cross L α β) (n+1)} (he : Plaza K) : Public (tele (install ∘ K) P) := h.lantern _ (installMeet he) (Foible.install K)
lemma ascend_coupon (h : Public P) {H : Legs (Row α β) (n+1)} (he : Plaza H) : coupon c _ (tele (plain ∘ H) P) =tele (fun i x y=> (H i).acts c x y) (coupon c _ P):= lantern_coupon id _ h (plainMeet he) (Foible.plain H) (fun _=> plain_gauge _)
lemma orient_coupon (h : Public P) {K : Legs (Cross g.count α β) (n+1)} (he : Plaza K) : coupon c _ (tele (install ∘ K) P)=tele (fun i x y=> installed g (K i) x y) (coupon f _ P):= lantern_coupon _ _ h (installMeet he) (Foible.install K) (fun _=> install_gauge g _)
lemma coupon_high {D : ℕ→ Side} (he : Tendsto (fun i=>(D i).val) atTop atTop) (hP : Public P) (hU : Public U) (hh : ∀ᶠ i in atTop, coupon (D i) _ P=coupon (D i) _ U) : P=U:= (hP.forever D).uniq he (hU.forever D) hh (by omega)
end bus
section finite
variable {α β : Type} [Fintype α] [Fintype β] {g : Duct α β}
-- add linearity with no geometry
omit [Fintype β] in
lemma tele_sub_fixed_finite {v v' : Legs (Duct α β) (n+1)} (h : ∀ i,v' i - v i= if i=0 then g else 0) (P : Page α (n+1)) : tele v' P-tele v P=tele (hitch g (crop v)) P := by
  have hg : v' 0= g + v 0:= (sub_eq_iff_eq_add).mp (by simpa using h (0:Fin (n+1)))
  have hp : crop v'=crop v:= funext fun i=> sub_eq_zero.mp ((h i.succ).trans (if_neg (Fin.succ_ne_zero i)))
  ext1 i; rw [Pi.sub_apply]; unfold tele; simp_rw [tsum_fintype]; rw [← sum_sub_distrib]; refine sum_congr rfl fun k _=>?_
  rw [← hitch_crop i, ← hitch_crop k]; simp_rw [metal_head,hitch_zero,crop_hitch,hg,hp]; simp [add_mul]
end finite
end Sheet
end YM.WilsonBulk

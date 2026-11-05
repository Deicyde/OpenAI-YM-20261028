import YM.WilsonBulk.Broadcast.Profiles

/-!
# Segue lemma for coherent transfers under flat linear changes of alphabet

Change of alphabet includes lumping positions for power estimates. Printing
commutes with these operations UNDER Hypothesis of common width for kernels,
own pre-L width unrelated to this bridge. Used for batch steps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Equiv Finset Matrix Bloch Lattice Laurent Pert.Bulk Work.F08
open scoped Topology Classical BigOperators ENNReal ContDiff
open PowerSeries (coeff constantCoeff)
variable {X Y α β : Type} {e n : ℕ} {p q σ θ : ℝ} {Λ L c f : Side} {F G : Legs (Duct X Y) n} {I : Record X} {A : Duct X Y}
-- packet transfer
@[simp] lemma tele_zero (F : Legs (Duct X Y) n) : tele F 0=0 := by unfold tele; ext1 x; simp [metal]
def lecture (A : Duct X Y) (V : Record X) : Record Y := fun e n=> Sheet.travel A (V e n)
lemma Document.lectured (h : Document I) (A : Duct X Y) : Document (lecture A I) :=
  ⟨fun i j p=> by rw [lecture, h.cap i j p,travel,tele_zero],fun i j=> travel_regular _ (h.coherent i j),fun i j p=> by rw [lecture,h.parity i j p,travel,tele_zero]⟩
lemma Cashless.lectured (h : Cashless I) (A : Duct X Y) : Cashless (lecture A I) := fun i=> by rw [lecture,h i,travel,tele_zero]
lemma Free.lectured (h : Free I) (A : Duct X Y) : Free (lecture A I):= fun i=> by rw [lecture,h i,travel,tele_zero]
lemma lecture_tape [Fintype X] [Fintype Y] (V : Record X) (A : Matrix X Y ℝ) : volumeTape (Sheet.lecture (fun i j=> A i j) V)=submit (quill A named) (volumeTape V) := by
  ext1 i; rw [quill_mono,coeff_parallel,tape_power,tape_power]; unfold capsule; dsimp only [lecture]
  rw [map_sum]; exact sum_congr rfl fun _ _=> travel_script _ _

abbrev Session (A : Duct (Market α) (Market β)) (n : ℕ) := ∀ σ:ℝ, 0<σ→ ∃ θ, 0<θ ∧ ∃ d : Duct (Market α) (Market β),Geometry (lawn α) (lawn β) σ θ d ∧ ∃ p q,AuditLine A d n p q
abbrev dean (D : ℕ→Side) (V : ∀ i, Record (Co (D i) α)) (A : Record (Market α)) := ∀ e n,n≠0→Proxy (fun i=>V i e n) (A e n)
variable {H J : Record (Market α)} [Fintype α] [Fintype β] {U : Text α n}
omit [Fintype α] [Fintype β] in
lemma Public.travel {F : Duct (Market α) (Market β)} (h0 : Session F n)
    (e : Cover→Cover) (h : ∀ x y b,F (roll (e b) _ x) (roll b _ y)=F x y) (g : Public U) : Public (Sheet.travel F U) := by
  obtain ⟨σ,p,hs,he⟩:= g.money; obtain ⟨θ,hh,d,H,A,B,h⟩:= h0 σ hs
  refine ⟨tele_roll e (fun _ x y b=>?_) g.style,?_⟩
  · apply_assumption
  cases n
  · exact ⟨1,0,one_pos,le_rfl,fun i=> Fin.elim0 i⟩
  exact ⟨θ,B*A^_ * p,hh,fare_const H (fun _=>h) he⟩ -- power mv
omit [Fintype α] [Fintype β] in
lemma issue_lecture {A : Duct (Market α) (Market β)} {F : Duct (Co f α) (Co c β)}
    (h0 : ∀ n, Session A n) (h : GaugeLine (small f α) (small c β) A F) (e : Cover→Cover) (hg : ∀ x y b,A (roll (e b) _ x) (roll b _ y)=A x y)
    (p : Pamphlet H) : lecture F (issue f H)=issue c (lecture A H) := by
  funext i n; cases n
  · simp [issue,lecture,coupon, Sheet.travel]
  rename_i n; symm; obtain ⟨σ,a,hs,hp⟩:= (p i (n+1)).money; obtain ⟨θ,hθ,g,hg',u,v,h₁⟩:= h0 _ σ hs
  exact ((p i _).travel (h0 (n+1)) e hg).orates_once c ((coupon_reads f (p i _).style).tele hg' (fun _ => h₁) hp hθ.le (fun _ => h)) (by omega)
lemma plainSession {F : Row α β} (hp : F.strip σ p) (hs : 0 < σ) (hq : 0 ≤ p) : Session (plain F) n := by
  intro θ ht; let a:=min (σ/(n+1)) θ
  have he : 0<a:=lt_min (div_pos hs (by positivity)) ht
  have hh : a/ (1:Side).val ≤ θ:= by rw [show (1:Side).val=1 from rfl,Nat.cast_one,div_one]; exact min_le_right .. -- inspect
  have h : a*(n+1)≤σ:= (le_div_iff₀ (by positivity : (0:ℝ)<n+1)).mp (min_le_left ..)
  have hv : a≤σ:= by have hk:= Nat.cast_nonneg (α:=ℝ) n; nlinarith
  refine ⟨a,he,spotCost 1 a,delta_shape he.le hh,_,_,plain_audited he.le hp hq hv (by nlinarith)⟩
lemma installSession {F : Cross L α β} (hp : F.strip σ p) (hs : 0 < σ) (hq : 0≤ p) : Session (install F) n := by
  intro θ ht; let a := min (σ/(n+1)) (θ*L.val); have hl : (0:ℝ) < L.val:= by positivity
  have he : 0<a:=lt_min (div_pos hs (by positivity)) (mul_pos ht hl)
  have hh : a/L.val ≤ θ := (div_le_iff₀ hl).mpr (min_le_right ..)
  have h : a*(n+1)≤σ:= (le_div_iff₀ (by positivity : (0:ℝ)<n+1)).mp (min_le_left ..)
  have hv : a≤ σ:= by have hk:= Nat.cast_nonneg (α:=ℝ) n; nlinarith
  exact ⟨a,he,spotCost L a,delta_shape he.le hh,_,_,install_audited hp hq he.le hv (by nlinarith)⟩
lemma dean.lecture {F : Row α β} (hσ : 0< σ) (h : F.strip σ p) (hp : 0 ≤ p) (D : ℕ→Side)
    (V : ∀ i,Record (Co (D i) α)) (he : dean D V H) : dean D (fun i=> Sheet.lecture (fun x y=> F.acts (D i) x y) (V i)) (Sheet.lecture (plain F) H) := by
  intro e n hn; cases n
  · contradiction
  rename_i n; refine (he e (n+1) hn).tele (fun _=> plain F) (fun i _ x y=> F.acts (D i) x y) id (fun i x y b=> plain_reads ..) (Eventually.of_forall fun i _=> plain_gauge F) ?_
  intro u hu; obtain ⟨s,hs,d,g,u,v,h⟩:= plainSession (n:=n+1) h hσ hp u hu
  exact ⟨s,hs,d,g,u,v,fun _=> h⟩
lemma dean.reached (F : Row α α) (V : Record (Market α)) (D : ℕ→Side) (hd : Tendsto (fun i=> (D i).val) atTop atTop)
    (U : ∀ i, Record (Co (D i) α)) (he : dean D U V) (ha : 0<σ) (h : F.strip σ p) (hp : 0 ≤ p) :
    dean D (fun i=> receive (pair (fun x y=> F.acts (D i) x y)) (U i) false) (receive (pair (plain F)) V true) := by
  exact Proxy.received hd (Proxy.always _ _ (Eventually.of_forall fun i=>plain_orates F) (Pervasive.plain_pair _) (lawn_pair h hp) ha) he
end YM.WilsonBulk.Sheet

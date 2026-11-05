import YM.WilsonBulk.Tickets.Inkling

/-!
# Root-preserving transformations and width budgets for polynomial tests.
    Ext stm encoded l1 support Norm; drop through Grade.N. Invariant stencil
    carries ALL moments. No color truncation in sumStem logic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Finset Lattice Laurent RG Pert.Bulk
open scoped Topology BigOperators Classical ENNReal
open Taylor (lineRead league)
open MvPolynomial (X C eval rename)
variable {α β γ : Type} {σ τ p q : ℝ} {n d : ℕ} {P U : Text α (n+1)}

/-- pair K test, all relative. collapse order e to moment. -/
def motif (V : Text α (n+1)) (x : Market α) (t : Legs α n) (v : Formula (Keys n)) := ∑' i,draft V x t i * lineRead i v
lemma wells (h : Within (lawn α) σ p P) (he : 0 < σ) (x : Market α) (v : Formula (Keys n)) (t : Legs α n) : HasSum (fun i:Slip n=> draft P x t i*lineRead i v) (motif P x t v) := (Taylor.sums_test _ he (draft_stamp h x t)).hasSum
lemma wells_paid (hp : Public P) (x : Market α) (v : Formula (Keys n)) (t : Legs α n) : HasSum (fun i:Slip n=> draft P x t i*lineRead i v) (motif P x t v) := by obtain ⟨σ,p,hs,h⟩:= hp.money; exact wells h hs ..
def motifL (P : Text α (n+1)) (h : Public P) (x : Market α) (t : Legs α n) : Formula (Keys n) →ₗ[ℝ] ℝ := {
    toFun:= motif P x t
    map_add' v w:= by unfold motif; simp only [lineRead,map_add,mul_add]; exact ((wells_paid h x v t).summable).tsum_add (wells_paid h x w t).summable
    map_smul' s v:= by
      unfold motif; simp only [RingHom.id_apply, smul_eq_mul,← MvPolynomial.C_mul', lineRead,map_mul,MvPolynomial.eval_C, mul_left_comm (draft _ _ _ _) s _,tsum_mul_left]
}
lemma motifL_point (hp : Public P) (x t v) : motifL P hp x t v=motif P x t v := rfl
-- enough for tariffs: ℝ budgets at varying G via this reader.
lemma motif_budget (h : Within (lawn α) σ p P) (he : 0 < σ) (x : Market α) (t : Legs α n) (v : List (Keys n)) : |motif P x t (league v)| ≤ momentWeight σ v.length*p := (norm_tsum_le_tsum_norm (Taylor.meters_league v he (draft_stamp h x t)|>.2.1)).trans (Taylor.meters_league v he (draft_stamp h x t)|>.2.2)
@[simp] lemma motif_void (x t) (v : Formula (Keys n)) : motif (0:Text α (n+1)) x t v=0 := by simp [motif,draft]
lemma motif_scale (x : Market α) (t : Legs α n) (s : ℝ) (u : Formula (Keys n)) : motif (s • P) x t u=s*motif P x t u := by simp [motif,draft,mul_assoc,tsum_mul_left]
lemma motif_add {U P : Text α (n+1)} (hu : Public U) (hp : Public P) (x t f) : motif (P+U) x t f=motif P x t f+motif U x t f := by unfold motif; simp_rw [show draft (P+U) x t = draft P x t+draft U x t from rfl,Pi.add_apply,add_mul]; exact (wells_paid hp x f t).summable.tsum_add (wells_paid hu x f t).summable
lemma motif_sub (h : Public P) (g : Public U) (x t u) : motif (P-U) x t u=motif P x t u-motif U x t u:= by rw [sub_eq_add_neg, show -U=(-1:ℝ) • U by simp, motif_add (g.scale _) h,motif_scale]; ring
lemma motif_eq (x : Market α) (f g : Formula (Keys n)) (t) (he : ∀ p:Slip n, lineRead p f = lineRead p g) : motif P x t f=motif P x t g := tsum_congr fun i=>congr_arg _ (he i)
lemma roll_draft (p : Pervasive P) (x y : Cover) (i : α) (t : Legs α n) : draft P (x,i) t=draft P (y,i) t := by
  ext1 v; unfold draft; nth_rw 2 [← p (x-y)]; congr 1; rw [hitch_comp]; congr 1
  · simp [roll_apply]
  ext1 j; simp only [put,Function.comp_apply,roll_apply]; congr 1; abel
lemma ticket_anchor (h : Pervasive P) (hz : ∀ i : α,∀ t (u: Formula (Keys n)), u.totalDegree < d→ HasSum (fun j : Slip n=>draft P (0,i) t j*lineRead j u) 0) : TicketNull d P:= by
  rintro ⟨x,i⟩ t u hu; change HasSum (fun j:Slip n=> draft P (x,i) t j * lineRead j u) 0; rw [roll_draft h x 0]; exact hz i t u hu
lemma TicketNull.basic (h : TicketNull d P) (i : Market α) (t : Legs α n) (u : Formula (Keys n)) (hu : u.totalDegree < d) : motif P i t u=0:= (h i t u hu).tsum_eq
lemma TicketNull.issue (hP : Public P) (h : ∀ i t l, (l:List (Keys n)).length<d → motif P (0,i) t (league l)=0) : TicketNull d P := by
  apply ticket_anchor hP.style; intro i t u hu; have he:=Taylor.list_suffices (w:=motifL P hP (0,i) t) u (h i t) hu; rw [← he]; exact wells_paid hP _ _ _
namespace TicketNull
lemma fewer {k : ℕ} (hp : TicketNull d P) (he : k≤d) : TicketNull k P := fun i f u hu=> hp i f u (lt_of_lt_of_le hu he) -- unknown k
lemma zeroDegree (P : Text α (n+1)) : TicketNull 0 P := fun _ _ _ h=> False.elim (Nat.not_lt_zero _ h)
lemma zero (d : ℕ) : TicketNull d (0:Text α (n+1)) := by intro x t u hu; simp
lemma plus (h : TicketNull d P) (f : TicketNull d U) : TicketNull d (P+U) := fun x t u hu=>by simpa [Pi.add_apply,add_mul] using (h x t u hu).add (f x t u hu)
lemma scale (h : TicketNull d P) (s : ℝ) : TicketNull d (s • P) := fun x t u hu=>by simpa [smul_eq_mul, mul_assoc] using (h x t u hu).mul_left s
lemma minus (hP : TicketNull d P) (hU : TicketNull d U) : TicketNull d (P-U) := by simpa only [neg_one_smul,sub_eq_add_neg] using hP.plus (hU.scale (-1))
lemma snipped (s : Finset β) (f : β→ Text α (n+1)) (h : ∀ i∈s,TicketNull d (f i)) : TicketNull d (∑ i∈s,f i) := by
  induction s using Finset.induction with
  | empty=> apply TicketNull.zero
  | insert a s ha ih=> rw [sum_insert ha]; exact (h a (mem_insert_self ..)).plus (ih fun a ha=>h _ (mem_insert_of_mem ha))
end TicketNull
end YM.WilsonBulk.Sheet

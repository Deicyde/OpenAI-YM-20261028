import YM.WilsonBulk.Tickets.Syntax

/-!
# Reindex test under new center and arbitrary-unused alphabet leg

The key source of rank 3-4 affine null for **positive grade normalization
DIFFERENCE**. Includes summability (all widths legal), obtains exactly
from lower contributions. True coordinate py all limbs. Need stickerless
(nonpositive ≤) grade orientation as tested at relative true displacement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Equiv Finset Lattice Laurent RG Precision Pert.Bulk Parapet Exterior
open scoped Topology BigOperators Classical ENNReal
open Taylor (lineRead league)
open MvPolynomial (X C eval rename aeval)
variable {α β γ : Type} {σ τ p q : ℝ} {n d k m : ℕ} {P : Text α (n+1)}

def invSlot (i : Fin n) (p : Slip n) : Slip n:= fun x=> if x.1=i then -p x else p x - p (i,x.2)
lemma snaps_back (i : Fin n) : Involutive (invSlot i) := by intro x; ext1 v; by_cases h:v.1=i <;> simp [invSlot,h]
def taxiSlot (i : Fin n) : Slip n ≃ Slip n:=(snaps_back i).toPerm _
def ports (i : Fin n) (x : Keys n) : Formula (Keys n):= if x.1=i then -X x else X x-X (i,x.2)
lemma tug_ink (i : Fin n) (x : Keys n) : (ports i x).totalDegree ≤ 1 := by
  have h (x : Keys n): (- MvPolynomial.X x : Formula _).totalDegree ≤ 1:= by
    rw [show -MvPolynomial.X x=(-1:ℝ) • (MvPolynomial.X x : Formula _) from by simp]; apply (MvPolynomial.totalDegree_smul_le ..).trans; simp
  unfold ports; split; exact h _
  rw [sub_eq_add_neg]; apply (MvPolynomial.totalDegree_add ..).trans; exact max_le (by simp) (h _)
lemma ghost (i : Fin n) (p : Slip n) (u : Formula (Keys n)) : lineRead (invSlot i p) u= lineRead p (aeval (ports i) u) := by
  change MvPolynomial.aeval _ u=MvPolynomial.aeval (fun i:Keys n=> (p i:ℝ)) (aeval _ u); symm; apply DFunLike.congr_fun (f:=(aeval _).comp (aeval _)); ext1 ⟨x,y⟩; by_cases h:x=i <;> simp [ports,h,invSlot]
lemma profile_return (x : Slip n) (i : Fin n) : profile i (invSlot i x)= -profile i x := by ext1 j; simp [profile,invSlot]
lemma offset_return (x : Slip n) (i j : Fin n) (h : j≠i) : profile j (invSlot i x)= profile j x-profile i x := by ext1 a; simp [profile,invSlot,h]
lemma swapping (x : α) (v : Slip n) (t : Legs α n) (i : Fin n) (b : Cover) :
    let f (j : α) (x : Legs α n) (u : Slip n):=hitch (b,j) (put b x u)
    roll (-profile i v) α ∘ ((f x t v) ∘ (swap (0:Fin (n+1)) i.succ))=f (t i) (Function.update t i x) (invSlot i v) := by
  intro f; ext1 j; cases j using Fin.cases
  · simp only [Function.comp_apply,swap_apply_left, f,hitch_zero,hitch_succ,roll_apply]; change (b+profile i v+-profile i v,_)=_; rw [add_neg_cancel_right]; rfl --?
  rename_i j; by_cases he : j=i
  · subst j; simp only [Function.comp_apply,swap_apply_right,f,hitch_zero,hitch_succ,roll_apply]; change (b+_,x)=(b+profile i (invSlot i v), Function.update t i x i); rw [Function.update_self,profile_return]
  rw [Function.comp_apply,Function.comp_apply,swap_apply_of_ne_of_ne (Fin.succ_ne_zero j) (fun h=>he (Fin.succ_inj.mp h))]; unfold f; rw [hitch_succ,hitch_succ]; change ((b+profile j v) + -profile i v,t j) = (b+profile j (invSlot i v), Function.update t i x j); rw [offset_return v i j he, sub_eq_add_neg,Function.update_of_ne he]; congr 1; abel
lemma taxes_rotate (hP : Regular P) (h : Pervasive P) (x : α) (l : Legs α n) (t : Slip n) (i : Fin n) : draft P (0,x) l t = draft P (0,l i) (Function.update l i x) (invSlot i t) := by
  dsimp only [draft]; have hx:= swapping x t l i 0; dsimp only at hx; rw [← hx,h,hP.eq]
lemma journal_laps (hp : Regular P) (h : Pervasive P) (x : α) (l : Legs α n) (i : Fin n) (p : Formula (Keys n)) : journal P x l p= journal P (l i) (Function.update l i x) (aeval (ports i) p) := by
  unfold journal motif; rw [← (taxiSlot i).tsum_eq (fun t=> draft P (0,x) l t*lineRead t p)]; apply tsum_congr; intro y; rw [show taxiSlot i y=invSlot i y from rfl]; rw [taxes_rotate hp h x l _ i, show invSlot i _=y from snaps_back i y]; rw [show lineRead _ p=lineRead y _ from ghost i y p]

lemma spare (n : ℕ) (a : List (Keys n)) (h : a.length<n) : ∃ i: Fin n, ∀ x ∈ a,x.1 ≠ i := by
  let p:= a.toFinset.image Prod.fst
  have hp : p.card< n:= by apply lt_of_le_of_lt (card_image_le) ((List.toFinset_card_le _).trans_lt h)
  obtain ⟨x,hx⟩ : ∃ x : Fin n,x∉p := by by_contra! h; rw [eq_univ_of_forall h,card_univ, Fintype.card_fin] at hp; omega
  exact ⟨x,fun i hi he=> hx (mem_image.mpr ⟨i,List.mem_toFinset.mpr hi,he⟩)⟩
lemma swift (n : ℕ) (i : Fin n) (q : List (Keys n)) (j : Axis) (h : ∀ x∈ q,x.1≠i) : outset (regionShift n j) (aeval (ports i) (league q))=aeval (ports i) (league q) := by
  have hw (x:Keys n) (hx:x.1≠i): outset (regionShift n j) (ports i x)=ports i x:= by unfold ports; rw [if_neg hx]; simp [outset,regionShift,cage]
  induction q with
  | nil=> simp
  | cons k q ih=> rw [Taylor.league_p,map_mul,map_mul,ih fun x hx=> h x (List.mem_cons_of_mem _ hx), MvPolynomial.aeval_X,hw k (h k List.mem_cons_self)]

lemma ticket_gain {G : Gauge} {T : Text (Cloth G) (n+1)} (hd : d≤n) (hp : Public T) (hr : Regular T) (h : TicketNull (d+1) (diss backed T)) : TicketNull d T := by
  refine TicketNull.issue hp fun i z u hu=>?_ ; obtain ⟨t,ht⟩:= spare n u (hu.trans_le hd); change journal T i z (league u)=0; rw [journal_laps hr hp.style i z t]; apply first_at_peer d n hd h hp _ _ (fun x=>swift n t u x ht); exact (Taylor.aeval_downgrade (w:=ports t) (tug_ink t) _).trans_lt ((Taylor.league_grade ..).trans_lt hu)
end YM.WilsonBulk.Sheet

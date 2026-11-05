import YM.WilsonBulk.Staves.Generator

/-!
# WT pressure at fixed horizon Valence/G grade: universal hard split power

Writes `diss` stencil on Cloth with site-mode on axis-0 token. Implement
lower terms from any previous Powers exactly by homogeneity. includes
x close small period shift coincidence. Operates on typed letters n (no path
curvature representatives yet). This buys all strict-event expansions later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Lattice Laurent Function Filter Bloch Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset Equiv
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {α β : Type} {G : Gauge} {i j : G.ColorIndex} {p q k n e : ℕ} {c : Side}

-- lifting first mode utilities
def castTail (t : α → Page α n) : Page α (n+1) := fun v=> t (v 0) (crop v)
def postage (W : Equiv (Fin n) (Fin q)) (t : Page α (n+1)) : Page α (q+1) := castTail fun x=>escort W (margin t x)
abbrev tailBuff (t : Page α (n+1)) := castTail fun x=> polish (margin t x)
@[simp] lemma post_mark (t : α → Page α n) (x : α) : margin (castTail t) x=t x := by ext1 i; simp [castTail, margin]
lemma tail_pass (t : Page α (n+1)) : castTail (margin t)=t := by ext1 i; simp [castTail,margin]
@[simp] lemma margin_zero (x : α) : margin (n:=n) 0 x=0:= rfl
@[simp] lemma margin_plus (p q : Page α (n+1)) (x : α) : margin (p+q) x=margin p x+margin q x:= rfl
@[simp] lemma margin_sub (p q : Page α (n+1)) (x : α) : margin (p-q) x=margin p x-margin q x:= rfl
@[simp] lemma margin_scale (p : Page α (n+1)) (x : α) (r : ℝ) : margin (r • p) x=r • margin p x:= rfl
@[simp] lemma margin_grabs (s : Finset β) (f : β→ Page α (n+1)) (x : α) : margin (∑ i∈s,f i) x=∑ i∈s,margin (f i) x:= by ext1 v; simp [margin]
lemma sum_cast_0 : castTail (fun _ : α=>(0:Page α n))=0 := rfl
abbrev CloudG (G : Gauge) (α : Type) (n : ℕ) := Page (α×Cloth G) n
-- bill: support duplicate a list (append) exactly, still carries V-kernel. Linear usable for budget. Not over diagonal product of tag budgets.
def tassel (b : Legs α q) (U : Page α k) : Page α (k+q) := fun v=> if keep k q v=b then U (snip k q v) else 0
@[simp] lemma tassel_pay (b : Legs α q) (u : Page α k) (v : Legs α k) (w : Legs α q) : tassel b u (Fin.append v w)= if w=b then u v else 0 := by simp [tassel]
@[simp] lemma tassel_zero (b : Legs α q) : tassel b (0:Page α k)=0 := by ext i; simp [tassel]
variable {X : Type}
-- patch

def cameo (d : Bool→PotentialForm→X→X) (t : Bool) (a : PotentialForm) (x : X) : X × PotentialForm := (d t a x,a)
def plume (d : Bool →PotentialForm→X→X) (t : Bool) (a : PotentialForm) (u i : G.ColorIndex) (v : Legs G.ColorIndex q) (V : CloudG G X (k+1)) : CloudG G X (k+q+1) :=
    castTail fun x=> let y:=cameo d t a x.1; if x.2=(coord 0,i) then tassel (selvedge y ∘ v) (margin V (selvedge y u)) else 0
-- f redundant param remove

def shaft (t : Bool) (u i : G.ColorIndex) := photo (lever t u i) q

def ribbons (d : Bool →PotentialForm→X→X) (t : Bool) (a : PotentialForm) (i : G.ColorIndex) (V : CloudG G X (k+1)) : CloudG G X (k+q+1) :=
    ∑ u:G.ColorIndex, ∑ v:Legs G.ColorIndex q, shaft (q:=q) t u i v • plume d t a u i v V

def spiro (d : Bool →PotentialForm→X→X) (V : CloudG G X (k+1)) (q) := tailBuff (∑ t:Bool,∑ a: PotentialForm,∑ i:G.ColorIndex, ribbons (q:=q) d t a i V)
-- strict transitions U_{e,r} with one later q paid.

def proceeding (d : Bool→PotentialForm→X→X) (V : Record (X × Cloth G)) (e n q : ℕ) : CloudG G X (n+1) := if h:q≤e ∧ q≤n then ((n-q+1:ℕ):ℝ) • postage (finCongr (Nat.sub_add_cancel h.2)) (spiro d (V (e-q) (n-q+1)) q) else 0

def squire (d : Bool→PotentialForm→X→X) (t : Bool) (P : CloudG G X (n+1)) : CloudG G X (n+1) := castTail fun x=> if x.2.1=coord 0 then ∑ a:PotentialForm, margin P (selvedge (cameo d t a x.1) x.2.2) else 0
abbrev diss (d : Bool→ PotentialForm→X→X) (P : CloudG G X (n+1)) := squire d true P - squire d false P
lemma shaft_zero (u i : G.ColorIndex) (t : Bool) (v : Legs G.ColorIndex 0) : shaft t u i v = if u=i then if t then 1 else -1 else 0 := by
  unfold shaft; have h := motive_zero t u i; rw [motive,ink_power,script_scalar] at h; rw [Subsingleton.elim v (show Legs G.ColorIndex 0 from Fin.elim0)]; exact MvPolynomial.C_injective (R:=ℝ) _ h
lemma tassel_0 (b : Legs α 0) (t : Page α k) : tassel b t=t := by ext1 i; rw [tassel,if_pos (Subsingleton.elim _ _)]; exact rfl
lemma margin_force {V T : Page α (k+1)} (h : ∀ x,margin V x=margin T x) : V=T := (tail_pass V).symm.trans ((congr_arg castTail (funext h)).trans (tail_pass T))
lemma spires_one (d : Bool →PotentialForm→X→X) (V : CloudG G X (k+1)) (h : Regular V) : spiro d V 0=diss d V := by
  apply margin_force
  intro x; rw [margin_sub]; unfold spiro tailBuff squire; simp_rw [ribbons,plume,shaft_zero,margin_grabs,margin_scale,post_mark,Fintype.sum_unique,tassel_0]; by_cases h' : x.2.1=coord 0
  · simp [Prod.ext_iff,h',ite_smul, smul_ite]; rw [← sub_eq_add_neg]; exact polish_eq ((Regular.summed fun _ _=> h.margin _).minus (Regular.summed fun _ _=> h.margin _))
  simp [Prod.ext_iff,h']
lemma proceeding_free (d : Bool → PotentialForm→X→X) (V : Record (X×Cloth G)) (hv : Based V) (e n : ℕ) : proceeding d V e n 0=((n+1:ℕ):ℝ) • diss d (V e (n+1)) := by
  rw [proceeding,dif_pos ⟨Nat.zero_le _,Nat.zero_le _⟩,spires_one d _ (hv (e-0) _), postage]; change _= ((n-0+1:ℕ):ℝ) • diss d (V (e-0) (n-0+1)); exact congr_arg _ (tail_pass _)
end Parapet
end YM.WilsonBulk

import YM.WilsonBulk.Tickets.Loom

/-!
# Lowest unhit measures -- exact before and after Reset. Uses link-origin
 spin transformations (true reading sign). Bounds for kinetic scalar consumed
 by next reset & reports. No universal/continuum beta content.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Equiv Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {V U : Text (Cloth G) 2} {c : Side} {e : ℕ} {σ p : ℝ} {I : Library G}
open Sheet.Taylor (lineRead league)
open MvPolynomial (X C)

-- normalize using a COMMON arbitrary color and transverse directions fixed 0 and 1.
def subdue (k : G.ColorIndex) (V : Text (Cloth G) 2) := -surge V 1 1 k k (noteP 0*noteP 0)
lemma subdue_price (k : G.ColorIndex) (hp : Within (lawn (Cloth G)) σ p V) (he : 0<σ) : |subdue k V| ≤ momentWeight σ 2*p:= by
  rw [subdue,abs_neg]; have ht:=motif_budget hp he (0,coord 1,k) (fun _=> (coord 1,k)) [μ 0, μ 0]; simpa only [Taylor.league_p, Taylor.league_empty,mul_one,subdue,surge,pageK,journal,noteP,show [μ 0,μ 0].length=2 from rfl] using ht -- list length defeq
lemma subdue_plus (hs : Public U) (hp : Public V) (k : G.ColorIndex) : subdue k (V+U)=subdue k V+subdue k U:= by unfold subdue surge pageK journal; rw [motif_add hs hp]; abel
lemma subdue_minus (hs : Public U) (hp : Public V) (k : G.ColorIndex) : subdue k (V-U)=subdue k V-subdue k U:= by unfold subdue surge pageK journal; rw [motif_sub hp hs]; abel
lemma subdue_pay (t : ℝ) (k : G.ColorIndex) (V : Text (Cloth G) 2) : subdue k (t • V)=t * subdue k V:= by unfold subdue surge pageK journal; rw [motif_scale]; ring
@[simp] lemma subdue_zero (k : G.ColorIndex) : subdue k (0 : Text (Cloth G) 2)=0:= by simp [subdue,surge,pageK,journal]
-- colour-one and directions-one lift. Need discharge Shelf shift from rank1 criterion

def allArks : Signed := ⟨1,fun _=>true⟩
def singleArk (i : Axis) : Signed := ⟨1,fun j=> decide (j=i)⟩
def publicArk (s : Equiv.Perm Axis) : Signed := ⟨s,fun _=> false⟩
lemma zero_spiro {α : Type} (d : Bool→PotentialForm→α→α) (e n) : spiro d (0:Page (α×Cloth G) (n+1)) e=0:= by rw [spiro,tailBuff]; apply margin_force; intro x; simp only [ribbons,plume,margin_zero,tassel_zero, ite_self,sum_cast_0,smul_zero,sum_const_zero,polish_zero]
lemma quad_empty (h : Whisper I) (hs : G.Simple) (e : ℕ) : diss backed (I e 2)=0 := by
  have hu := submission (I:=I) h e 1
  have hz : strategy backed I e 1=0 := sum_eq_zero fun i _=> by
    rw [proceeding]; split; next h'=>
      have hX:i=0:= by omega
      subst i; simp only [Nat.zero_add,tsub_self,Nat.zero_add]; rw [color_null h hs (e-1), zero_spiro]; simp only [postage,escort_zero,margin_zero]; exact smul_zero _
    exact rfl
  rw [hu,hz]; simp

variable (h : Whisper I) (hs : G.Simple) (k : G.ColorIndex) (hz : subdue k (I e 2)=0)
include h hs
local notation "lens" => signalK (h.palm e 2)
lemma optic (i j : G.ColorIndex) (x y a : Axis) : lens x y i j (noteP a)=0 := by
  let A := drift allArks y-drift allArks x; let g:=(- (1:ℝ)) • noteP a + ((A a:ℤ):ℝ) • (1:Formula (Keys 1)); let w:= noteP a
  have ht : lens x y i j w = lens x y i j g := by
    have hp : ∀ v : Cover,lineRead (cage (allArks.act v+drift allArks y-drift allArks x)) (noteP (allArks.perm a))= lineRead (cage v) g:= by
      intro v; unfold noteP lineRead g; rw [map_add,MvPolynomial.eval_X, ← MvPolynomial.C_mul', ← MvPolynomial.C_mul' (a:=((A a:ℤ):ℝ))]; simp only [μ,cage,Pi.add_apply,Pi.sub_apply,Int.cast_sub, Int.cast_add,map_mul,MvPolynomial.eval_C, noteP, MvPolynomial.eval_X,map_one, spin_axes allArks v a]; change -1* _ + _-_= (-1:ℝ)*_+ _*1; simp only [A,Pi.sub_apply,Int.cast_sub,show allArks.perm a=a from rfl]; ring
    have he:= surge_versus h e allArks x y i j (noteP _) g hp; simp only [flagFee,allArks,↓reduceIte,neg_mul_neg,mul_one,one_mul] at he; exact he
  unfold w g at ht; rw [map_add,map_smul,map_smul,pulse_empty _ (quad_empty h hs e),smul_zero,add_zero,neg_one_smul] at ht; linarith only [ht]
lemma optics_two (i j : G.ColorIndex) (x y a b : Axis) (s : Signed) :
    lens (s.perm x) (s.perm y) i j (noteP (s.perm a)*noteP (s.perm b))=flagFee s x * flagFee s y * (flagFee s a * flagFee s b)*lens x y i j (noteP a*noteP b) := by
  let d (a : Axis) := (((drift s y-drift s x) (s.perm a):ℤ):ℝ)
  let f (x:Axis):= noteP (s.perm x); let g (x:Axis):= flagFee s x • noteP x+d x • (1:Crusade)
  let p : Crusade:= (flagFee s a * flagFee s b) • (noteP a*noteP b)+(flagFee s a*d b) • noteP a+ (d a*flagFee s b) • noteP b+(d a*d b) • (1:Crusade)
  have hf (j : Axis) (v : Cover) : lineRead (cage (s.act v+drift s y-drift s x)) (f j)= lineRead (cage v) (g j):= by
     unfold f g noteP lineRead d; rw [← MvPolynomial.C_mul', ← MvPolynomial.C_mul' (a:=(((drift s y-drift s x) (s.perm j):ℤ):ℝ)), map_add]; simp only [map_mul,map_one,MvPolynomial.eval_X,MvPolynomial.eval_C,μ,cage,Pi.add_apply,Pi.sub_apply,Int.cast_sub,Int.cast_add, spin_axes]; ring
  have hp : g a*g b=p := by
     unfold p g; simp_rw [← MvPolynomial.C_mul', map_mul]; ring
  have he : lens (s.perm x) (s.perm y) i j (f a*f b)=flagFee s x *flagFee s y* lens x y i j (g a*g b):= surge_versus h e s x y i j _ _ (by intro i; unfold lineRead; rw [map_mul,map_mul]; exact congr_arg₂ (·*·) (hf a i) (hf b i))
  rw [show lens (s.perm x) (s.perm y) i j (noteP (s.perm a)*noteP (s.perm b))= _ from he,hp]; unfold p; simp only [map_add,map_smul,optic h hs,pulse_empty _ (quad_empty h hs e), smul_eq_mul]; ring
end YM.WilsonBulk.Parapet

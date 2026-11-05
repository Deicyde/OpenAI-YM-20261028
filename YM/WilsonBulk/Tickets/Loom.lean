import YM.WilsonBulk.Tickets.Orbit

/-!
# Charge rank two Ω convention: true lattice displacement, no half-image
 barycenter. `reib` polynomial moments on cover-units territories. Choir
 decomp & rank2 stencil Sym. Enough for any post transform costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Equiv Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {V : Text (Cloth G) 2} {c : Side} {e : ℕ} {I : Library G}
open Sheet.Taylor (lineRead league)
open MvPolynomial (X C)

abbrev Crusade := Formula (Keys 1)
abbrev pageK (x i : Cloth G) (V : Text (Cloth G) 2) := journal (n:=1) V x (fun _ => i)
def surge (V : Text (Cloth G) 2) (x y : Axis) (i j : G.ColorIndex) (u : Crusade) := pageK (coord x,i) (coord y,j) V u
def signalK (h : Public V) (x y : Axis) (i j : G.ColorIndex) : Crusade →ₗ[ℝ] ℝ := motifL V h (0,(coord x,i)) (fun _=> (coord y,j))
abbrev μ (x : Axis) : Keys 1 := (0,x)
def noteP (x : Axis) : Crusade:= X (μ x)
@[simp] lemma remote_X (x y : Axis) : remote y (noteP x) = if y=x then -1 else 0 := by
  unfold noteP; simpa only [mul_one] using remote_law (n:=1) y 0 x (1:Crusade) (map_one _)
lemma pulseK (h : Public V) (hz : diss backed V=0) (u : Crusade) (x : Axis) (i j : G.ColorIndex) : ∑ a : Axis, signalK h a x i j (remote a u)=0 := by
  rw [show (∑ a:Axis,signalK h a x i j (remote a u))=_ from (motif_diss h i (fun _=> (coord x,j)) u).symm]; simp [hz,journal]
lemma pulse_empty (h : Public V) (hz : diss backed V=0) (x y : Axis) (i j : G.ColorIndex) : signalK h x y i j 1=0 := by
  have he:= pulseK h hz (noteP x) y i j; simp_rw [remote_X,apply_ite (signalK _ _ _ _ _), map_neg, map_zero] at he; simpa using he

-- spin cost transfer
lemma act_pair (h : Whisper I) (e : ℕ) (s : Signed) (x y : Cover) (a b : Axis) (i j : G.ColorIndex) :
    I e 2 (two (s.act x+drift s a,(coord (s.perm a),i)) (s.act y+drift s b, (coord (s.perm b),j)))=flagFee s a*flagFee s b*I e 2 (two (x,coord a,i) (y,coord b,j)) := by
  have hp:= h.equivariant s (two (x,coord a,i) (y,coord b,j)) e; rw [Fin.prod_univ_two] at hp
  -- unfold to axis orientation; use comp_reduce
  have he (v:Cover) (a:Axis) (i:G.ColorIndex) : banners s (v,coord a,i)=(s.act v+drift s a,coord (s.perm a),i) := by simp [banners,orient, ← coord_map]
  let u:= (x,(coord a,i)); let v:Mark G:= (y,(coord b,j)); rw [show (banners s ∘ two u v)=two (banners s u) (banners s v) from funext (fun z=>by fin_cases z <;> rfl), he,he, show orient ((two u v) 0)=a from axisEquiv.symm_apply_apply a,show orient (two u v 1)=b from axisEquiv.symm_apply_apply b] at hp; exact hp

def singleSlip : Cover ≃ Slip 1 where
  toFun x:= cage x
  invFun x:= profile 0 x
  left_inv _:= rfl
  right_inv x:= by ext1 ⟨i,j⟩; rw [Fin.fin_one_eq_zero i]; rfl
lemma drafted_budget (p : Slip 1) (x y : Cloth G) : draft V (0,x) (fun _=>y) p=V (two (0,x) (profile 0 p,y)) := by
  unfold Sheet.draft; congr 1; ext1 j; fin_cases j
  · rfl
  change ((0 :Cover)+_,y)=_; rw [zero_add]; rfl -- layout
lemma lyric (V : Text (Cloth G) 2) (x y : Axis) (i j : G.ColorIndex) (p : Crusade) : surge V x y i j p=∑' u: Cover,V (two (0,coord x,i) (u,coord y,j))*lineRead (cage u) p := by
  unfold surge pageK journal motif; rw [← singleSlip.tsum_eq]; apply tsum_congr; intro x; rw [drafted_budget]; rfl
lemma spin_axes (s : Signed) (u : Cover) (i : Axis) : (((s.act u) (s.perm i):ℤ):ℝ)=flagFee s i *((u i:ℤ):ℝ) := by rw [Signed.act_at]; unfold flagFee; split <;> simp
lemma surge_versus (h : Whisper I) (e : ℕ) (s : Signed) (x y : Axis) (i j : G.ColorIndex) (f g : Crusade)
    (he : ∀ z:Cover,lineRead (cage (s.act z+drift s y-drift s x)) f = lineRead (cage z) g) :
    surge (I e 2) (s.perm x) (s.perm y) i j f=flagFee s x * flagFee s y * surge (I e 2) x y i j g := by
  rw [lyric,lyric]
  let r: Cover≃Cover:= (s.actEquiv (R:=ℤ)).toEquiv.trans (Equiv.addRight (drift s y-drift s x)); rw [← r.tsum_eq (fun z=> I _ _ _*lineRead _ _),← tsum_mul_left]; refine tsum_congr fun z=> ?_
  have hz : r z=s.act z+drift s y-drift s x:= by unfold r; rw [Equiv.trans_apply]; change s.act z+(drift s y-drift s x)=_; abel
  rw [hz,he]; refine Eq.trans (congrArg (· * _ : ℝ→ℝ) ?_) (by rw [mul_assoc (flagFee _ _ * _)]); conv_lhs => rw [← (h.palm _ _).style (drift s x)]
  rw [← act_pair h]; congr 1; ext1 i; fin_cases i <;> simp [two, roll_apply, Signed.act_zero] -- norm_number

lemma color_price (h : Whisper I) (hs : G.Simple) (k i j : G.ColorIndex) (x y : Axis) (p : Crusade) (e : ℕ) : surge (I e 2) x y i j p= if i=j then surge (I e 2) x y k k p else 0 := by
  rw [lyric, lyric]; let Q:=I e 2
  have he (v : Cover) : Q (two (0,coord x,i) (v,coord y,j))=if i=j then Q (two (0,coord x,k) (v,coord y,k)) else 0 := h.pair_plate hs e (0,coord x) (v,coord y) i j k
  split
  next h=> exact tsum_congr fun u=> by rw [show I e 2 _ =_ from (he u).trans (if_pos h)]
  next h=> simp_rw [show ∀ z:Cover,I e 2 (two (0,coord x,i) (z,coord y,j))=0 from fun z=> (he z).trans (if_neg h)]; simp
end YM.WilsonBulk.Parapet

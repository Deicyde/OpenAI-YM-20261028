import YM.Next.RANK.Pennant
import YM.Next.RANK.Tilt



/-!
# Polynomial appointment over the pinned transfer gates

Read origin lift always from same k. Telescope through sh and full Lead to
compare station endpoint. A branch not meeting support condition will have
zero cut result; not needed to start the recursion. Explicit polynomial norm
invoice. No normalized physical expectation estimate here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {S : Schedule} {C : Family G} {i k l j m p q n D N d : ℕ}

abbrev Lead (G : Gauge) (S : Schedule) (p : ℕ) := ∀ j, Valve (Chamber G S (j+1) p) (Chamber G S j p)

def track (A : AtlasData G S p) : Lead G S p := fun j=>⟨A.path j,stageCov A j⟩
variable (R : Lead G S p)

def shelve (h : j≤k) (W : poly (Chamber G S k p)) := Nat.decreasingInduction (motive:=fun i _=> poly (Chamber G S i p))
    (fun i _ q=> (R i).read q) W h
lemma shelving (h : j<k) (F) : shelve R h.le F= (R j).read (shelve R (show j+1≤k from h) F):=Nat.decreasingInduction_succ_left ..
lemma center_shelf (k) (F) : shelve R (k:=k) le_rfl F=F:= Nat.decreasingInduction_self ..
lemma forecast (X : AtlasData G S p) (h : j≤k) (V) : shelve (track X) h V= preserve X V j h:= rfl

def oneRoot (H : Fin n → poly (Chamber G S k p)) (h : j≤k) (a : Fin n) := shelve R h (H a)
def twoRoot (H : Fin n → poly (Chamber G S k p)) (h : j≤k) (a : Twin n) := shelve R h (H a.val.1 * H a.val.2)
def polygon (H : Fin n → poly (Chamber G S k p)) (h : j≤k) : pennant n → poly (Chamber G S j p)
  | .inl x=> oneRoot R H h x
  | .inr x=> twoRoot R H h x-oneRoot R H h x.val.1 * oneRoot R H h x.val.2
lemma root_e (H : Fin n → _) (h : j≤k) (x : Twin n) : twoRoot R H h x=polygon R H h (.inr x)+oneRoot R H h x.val.1 * oneRoot R H h x.val.2:= by rw [polygon,sub_add_cancel]
lemma page (H) (h : j<k) (x : Fin n) : polygon R H h.le (.inl x) = (R j).read (polygon R H (show j+1≤k from h) (.inl x)):=shelving R h _
lemma second_page (H) (h : j<k) (x : Twin n) :
    let hi:j+1≤k:= h
    polygon R H h.le (.inr x)=(R j).read (polygon R H hi (.inr x))+(R j).read (polygon R H hi (.inl x.val.1)*polygon R H hi (.inl x.val.2)) -
      polygon R H h.le (.inl x.val.1)*polygon R H h.le (.inl x.val.2):= by
  intro hi; conv_lhs => rw [show polygon R H h.le (.inr x)=twoRoot R H h.le x-oneRoot R H h.le x.val.1*oneRoot R H h.le x.val.2 from rfl,show twoRoot R H h.le x=(R j).read (twoRoot R H (show j+1≤k from h) x) from shelving R h _,root_e,_root_.map_add]
  rfl

section tilt
variable {X : AtlasData G C.S p} {Q : Rep G (C.side k p)}
-- identify trial sources when the calibrated polynomial is returned by the same Atlas.K

def lifted (_X : AtlasData G S p) (P : poly (slotC G i)) (a : Cover) (k) (h : 4*i≤l) :=
    rename (fun x : trimV l G=> body (P:=S) (k:=k) (p:=p) a x.val) (rename (calls h) P)

-- frame-invariance of control under these shifts. Better derive from κ sector.
def invariantAt (k l p : ℕ) (X : AtlasData G C.S p) := ∀ x : Cover,control X (k:=k) x l=control X (k:=k) 0 l

def prefaced (F : StampDuty C k N p d D Q q X) (v : C.label d) (s : Cover) := lifted X (F.W v) s k F.r
variable {F : StampDuty C k N p d D Q q X}
lemma genesis (v : C.label d) (s) (hp : invariantAt (C:=C) k (wood C.path.levels k) p X) : prefaced F v s=
    rename (fun x : trimV (wood C.path.levels k) G=> body (P:=C.S) (k:=k) (p:=p) s x.val) (milk (-(control X (k:=k) s (wood C.path.levels k))) (F.heater v)):= by
  rw [hp s,F.head,warms]
  have he (Z : Type) (M : Normal.Symmetric Z) : - M + M= 0 := by
    apply Normal.Symmetric.ext; funext i j; exact neg_add_cancel _
  rw [he,Normal.froze];rfl

lemma notices (v : Fin n→ C.label d) (s : Fin n→Cover) (hn : n≤2) (hk : j≤ k) (hp : invariantAt (C:=C) k (wood C.path.levels k) p X) (u : Chamber G C.S j p→ℝ) :
    ∀ i, (Cumulus X s hk F.heater v u).part (tale i).val = text u (polygon (track X) (fun i=> prefaced F (v i) (s i)) hk i):= by
  let P:=fun i:Fin n=>prefaced F (v i) (s i)
  let Q:=Answer X s hk (fun i=> F.heater (v i)) (fun i=>(u i:ℂ))
  have he (i : Glyph.modes (Fin n)) : Q.part i=text u (shelve (track X) hk (∏ a∈i.val, P a)) := by
    rw [forecast]; unfold P; simp_rw [genesis _ _ hp]; rfl
  let W:= Cumulus X s hk F.heater v u
  have h : Expands W Q:=connected_spec Q (phased X s hk _ _)
  have h1 i : W.part (Glyph.slot i)=text u (oneRoot (track X) P hk i):= by rw [← spark_single hn h,he,show _ = _ from (show (Glyph.slot i).val={i} from rfl),Finset.prod_singleton]; rfl
  rintro (a|a)
  · exact h1 a
  have hx := (crossings hn h a).symm.trans (he _)
  rw [show (tale (Sum.inr a)).val.val={a.val.1,a.val.2} from rfl, Finset.prod_pair a.property.ne,h1,h1] at hx
  dsimp only [polygon]; unfold text; rw [_root_.map_sub,map_mul]
  apply eq_sub_of_add_eq hx

end tilt

-- pricing constants

variable (c : ℝ)
def hike (d b : ℕ) : ℝ:= (crest c d)^b

lemma ample (j D : ℕ) (h : 1≤c) : 0 ≤ hike c D j := pow_nonneg (zero_le_one.trans (pay_crest h D)) _

variable {c}
lemma flying (P) (hk : j≤k) (hB : 1≤c) (h : ∀ i, j ≤ i → i<k → (R i).Fair c) (hp : MvPolynomial.totalDegree P≤d) : coin (shelve R hk P) ≤ coin P*hike c d (k-j) ∧ (shelve R hk P).totalDegree ≤ d:= by
  induction hk using Nat.decreasingInduction with
  | self=> rw [center_shelf, Nat.sub_self,hike,pow_zero,mul_one]; exact ⟨le_rfl,hp⟩
  | of_succ i hi ih=>
    obtain ⟨he,ht⟩:= ih (fun j hj=> h j (by omega))
    rw [shelving _ hi]
    obtain ⟨hx,hy⟩:= crux (h i le_rfl hi) _ d ht
    have hv := mul_le_mul_of_nonneg_right he (zero_le_one.trans (pay_crest hB d))
    exact ⟨hx.trans (hv.trans_eq (by unfold hike; rw [show k-i= (k-(i+1))+1 from by omega,pow_succ,mul_assoc])),hy⟩
lemma diminish {E} (P) (hk : j ≤ k) (hB : 1≤c) (hE : 0 ≤ E) (R' : Lead G S p) (h : ∀ i, j ≤ i → i<k → Awake (R i) (R' i) c E) (hp : totalDegree P≤d) :
    coin (shelve R hk P-shelve R' hk P) ≤ coin P * hike c d (k-j) * (k-j:ℕ) * E:= by
  induction hk using Nat.decreasingInduction with
  | self=> rw [center_shelf,center_shelf,sub_self,Nat.sub_self]; simp only [coin,pay_nothing,Nat.cast_zero,mul_zero,zero_mul,le_refl]
  | of_succ i hi ih=>
    let u:=shelve R (show i+1≤k from hi) P; let v:=shelve R' (show i+1≤k from hi) P
    obtain ⟨h₁,h₂⟩:= flying R P (show i+1≤k from hi) hB (fun j hj hJ=> (h j (by omega) hJ).pay) hp
    obtain ⟨h₃,h₄⟩:= flying R' P (show i+1≤k from hi) hB (fun j hj hJ=> (h j (by omega) hJ).cut) hp
    have hx:= ih (fun j hj hJ=> h j (by omega) hJ)
    have hv:= crux (h i le_rfl hi).cut (u-v) d (by grw [sub_eq_add_neg,totalDegree_add .., show -v=(-1:ℂ)•v by simp,totalDegree_smul_le]; exact max_le h₂ h₄)
    let f := (R i).read; let g:=(R' i).read
    rw [shelving R hi,shelving R' hi,show f u-g v=f u-g u+g (u-v) by rw [_root_.map_sub]; abel]; have he:=pay_crest hB d
    apply (taller _ zero_le_one ..).trans
    apply le_trans (add_le_add ((crossing (h i le_rfl hi) u d h₂).trans (mul_le_mul_of_nonneg_right h₁ (mul_nonneg hE (zero_le_one.trans he))))
      (hv.1.trans (mul_le_mul_of_nonneg_right hx (zero_le_one.trans he))))
    rw [show k-i=k-(i+1)+1 from by omega]; unfold hike; rw [pow_succ]; exact le_of_eq (by push_cast; ring)

end YM.Next.Rank.Tapes

import YM.Next.STATIONARY.Joint.OnShell
import YM.Next.STATIONARY.Shape.GaugeJets


set_option autoImplicit false
/-!
# Jets for real-analytic rectangles, tested at complex amplitude

At zero with real scalar coordinates. Signs left-to-right column convention.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} [Fintype ι] [DecidableEq ι]

def art (U : Corn ι → Matrix α β ℝ) (n : ℕ) (p : Fin n → Phase ι) := Matrix.of fun i j => beat (fun a => U a i j) 0 n p
def cardM (U : Corn ι→ Matrix α β ℝ) := approached (U 0)
def seat (U : Corn ι→ Matrix α β ℝ) (p : Phase ι) := art U 1 ![p]
def cart (U : Corn ι→ Matrix α β ℝ) (p q : Phase ι) := art U 2 ![p,q]
lemma seating (U : Corn ι →Matrix α β ℝ) (p : Corn ι) : seat U (axes p)=approached (directionM U 0 p) := by
  unfold seat art; ext i j; simp only [Matrix.of_apply]
  rw [show ![axes p]=axes ∘ (![p]:Fin 1 → _) by funext i; fin_cases i <;> rfl,beat_real,iteratedFDeriv_one_apply]; rfl
lemma carting (U : Corn ι → Matrix α β ℝ) (p q : Corn ι) : cart U (axes p) (axes q)=approached (bendM U 0 p q) := by
  unfold cart art; ext i j; simp only [Matrix.of_apply]
  rw [show ![axes p,axes q]=axes ∘ (![p,q]:Fin 2 → _) by funext i; fin_cases i <;> rfl,beat_real]; rfl

section slots
variable {X : Type} [Add X] [SMul ℂ X]
/-- For extension principle. Only need i-linear additive expansion. -/
def Leads (p : Phase ι → X) := ∀ u v : Corn ι,p (axes u+Complex.I • axes v)=p (axes u)+Complex.I • p (axes v)
lemma Leads.buys {p q : Phase ι → X} (h : Leads p) (he : Leads q) (hu : ∀ v, p (axes v)=q (axes v)) (b) : p b=q b := by
  rw [show b=axes (fun i => (b i).re)+Complex.I • axes (fun i => (b i).im) by funext i; simp [axes]; rw [mul_comm Complex.I, Complex.re_add_im],h,he,hu,hu]
lemma Leads.two {p q : Phase ι → Phase ι → X} (h : ∀ i, Leads fun j => p j i) (he : ∀ i, Leads (p i))
    (hv : ∀ i, Leads fun j => q j i) (hu : ∀ i, Leads (q i)) (hw : ∀ a b, p (axes a) (axes b)=q (axes a) (axes b)) (y z) : p y z=q y z :=
    (h z).buys (hv z) (fun a => (he (axes a)).buys (hu (axes a)) (hw a) z) y
end slots
lemma Leads.pulse {n : ℕ} (p : RecordM ℂ (Fin n) ι) (u : Fin n → Phase ι) (i : Fin n) : Leads fun a => p (update u i a) := fun b c => by dsimp only; rw [p.map_update_add,p.map_update_smul]

lemma seat_e (U : Corn ι→ Matrix α β ℝ) : Leads (seat U) := by
  intro u v; ext i j
  unfold seat art; simp only [Matrix.of_apply,Matrix.add_apply,Matrix.smul_apply]
  have he (p : Phase ι) : (![p]:Fin 1→_)=update (0:Fin 1→Phase ι) 0 p := by funext i; fin_cases i; simp
  rw [he (axes u+Complex.I • axes v),he (axes u),he (axes v)]; exact Leads.pulse _ _ _ _ _
lemma left_beat (F : Corn ι → ℝ) (p : Phase ι) : Leads fun q => beat F 0 2 ![q,p] := by
  intro u v
  have he (q) : (![q,p]:Fin 2→_)=update ![0,p] 0 q := by funext i; fin_cases i <;> simp
  dsimp only;  rw [he (axes u+Complex.I • axes v),he (axes u),he (axes v)]; exact Leads.pulse _ _ _ _ _
lemma right_beat (F : Corn ι → ℝ) (p : Phase ι) : Leads fun q => beat F 0 2 ![p,q] := by
  intro u v
  have he (q) : (![p,q]:Fin 2→_) = update ![p,0] 1 q := by funext i; fin_cases i <;> simp
  dsimp only;  rw [he (axes u+Complex.I • axes v),he (axes u),he (axes v)]; exact Leads.pulse _ _ _ _ _
lemma cart_left (U : Corn ι→ Matrix α β ℝ) (p : Phase ι) : Leads fun q => cart U q p := by intro u v; ext i j; exact left_beat (fun a => U a i j) p u v
lemma cart_right (U : Corn ι→ Matrix α β ℝ) (p : Phase ι) : Leads (cart U p) := by intro u v; ext i j; exact right_beat (fun a => U a i j) p u v

section assembly
variable {X : Type} [AddCommGroup X] [Module ℂ X] {p q : Phase ι → X}
lemma Leads.plus (h : Leads p) (hz : Leads q) : Leads (fun v => p v+q v) := fun u v => by dsimp only; rw [h,hz,smul_add]; abel
lemma Leads.sub (h : Leads p) (hz : Leads q) : Leads (fun v => p v-q v) := fun u v => by dsimp only; rw [h,hz,smul_sub]; abel
lemma Leads.neg (h : Leads p) : Leads (fun v => -p v) := fun u v => by dsimp only; rw [h,smul_neg,neg_add',sub_eq_add_neg]
lemma Leads.cost (h : Leads p) (a : ℂ) : Leads (fun v => a • p v) := fun u v => by dsimp only; rw [h,smul_add,smul_comm _ Complex.I]
variable [Fintype β]
lemma Leads.upper {P : Phase ι → CompM α β} (h : Leads P) (K : CompM β γ) : Leads fun q => P q*K := fun u v => by dsimp only; rw [h,Matrix.add_mul,Matrix.smul_mul]
lemma Leads.lower {P : Phase ι → CompM β γ} (h : Leads P) (K : CompM α β) : Leads fun q => K*P q := fun u v => by dsimp only; rw [h,Matrix.mul_add,Matrix.mul_smul]
lemma Leads.tab {P : Phase ι → CompM β β} (h : Leads P) : Leads fun q => (P q).trace := fun u v => by dsimp only; rw [h,trace_add, trace_smul]
end assembly

lemma Memo.peers [Fintype α] [Fintype β] {U : Corn ι → Matrix α β ℝ} {x : Corn ι} (h : Memo U x) : ∀ᶠ z in 𝓝 x,Memo U z := eventually_all.mpr fun i => eventually_all.mpr fun j => (h i j).eventually (by simp)

lemma prom_addition (A B : Matrix α β ℝ) : approached (A+B)=approached A+approached B := by ext; simp [approached]
lemma prom_tone (A : Matrix α β ℝ) (a : ℝ) : approached (a • A)=(a:ℂ) • approached A := by ext; simp [approached]

variable {U V : Corn ι → Matrix α β ℝ} {p q : Phase ι}
lemma art_raw (U : Matrix α β ℝ) {n : ℕ} (h : n≠0) (v : Fin n → Phase ι) : art (fun _ => U) n v=0 := by
  ext i j; unfold art beat enlarge; rw [Matrix.of_apply,recording_apply]; simp [iteratedFDeriv_const_of_ne h]
lemma art_plus (h : Memo U 0) (he : Memo V 0) {n : ℕ} (p : Fin n→Phase ι) : art (U+V) n p=art U n p+art V n p := by
  ext i j; unfold art; simp only [Pi.add_apply, Matrix.add_apply,Matrix.of_apply]
  have H : beat (fun a => U a i j+V a i j) 0 n=beat (fun a => U a i j) 0 n+beat (fun a => V a i j) 0 n := by
    apply enlarge_unique; intro v; rw [_root_.add_apply,beat_real,beat_real,beat_real]; rw [show iteratedFDeriv ℝ n (fun a => U a i j+V a i j) 0=_ from iteratedFDeriv_add_apply (h i j |>.of_le le_top) (he i j |>.of_le le_top), _root_.add_apply, Complex.ofReal_add]
  rw [H,_root_.add_apply]
lemma art_smul (a : ℝ) (h : Memo U 0) {n : ℕ} (p : Fin n→Phase ι) : art (a • U) n p=(a:ℂ) • art U n p := by
  ext i j
  suffices he : beat (fun z => a • U z i j) 0 n=(a:ℂ) • beat (fun z => U z i j) 0 n from DFunLike.congr_fun he p
  apply enlarge_unique; intro v
  rw [_root_.smul_apply,beat_real,beat_real,show iteratedFDeriv ℝ n (fun z => a • U z i j) 0= a • iteratedFDeriv ℝ n (fun z => U z i j) 0 from iteratedFDeriv_const_smul_apply (i:=n) (a:=a) ((h i j).of_le le_top)]; simp

section ledger
variable [Fintype α] [Fintype β] [Fintype γ] {W : Corn ι→ Matrix β γ ℝ} (h : Memo U 0) (hv : Memo W 0)
include h hv
lemma seat_prod : seat (fun x => U x*W x) p = seat U p * cardM W +cardM U * seat W p := by
  refine Leads.buys (seat_e _) (((seat_e _).upper (cardM W)).plus ((seat_e W).lower (cardM U))) ?_ p
  intro i; rw [seating,seating,seating,direction_prod h hv,prom_addition,prom_mul,prom_mul]; rfl
lemma cart_prod : cart (fun x => U x*W x) p q = cart U p q * cardM W + seat U q * seat W p + seat U p * seat W q + cardM U * cart W p q := by
  refine Leads.two (cart_left _) (cart_right _)
    (fun i => ((((cart_left _ i).upper _).plus ((seat_e _).lower (seat U i))).plus ((seat_e U).upper (seat W i))).plus ((cart_left W i).lower (cardM U)))
    (fun i => ((((cart_right _ i).upper _).plus ((seat_e _).upper _)).plus ((seat_e _).lower _)).plus ((cart_right W i).lower (cardM U)))
    ?_ p q
  intro a b
  simp only [seating,carting,cardM]
  simp only [← prom_mul,← prom_addition]
  apply congr_arg approached
  rw [← coins_M (Memo.cross h hv)]
  have he := directions_congr (M:=fun v => directionM (fun a => U a*W a) v b) (N:=fun v => directionM U v b * W v+U v * directionM W v b) (x:=0) (u:=a) (by filter_upwards [h.peers,hv.peers] with x h he; exact direction_prod h he _)
  rw [he]
  ext i j
  let X z := directionM U z b * W z; let Y := fun z => U z * directionM W z b
  have hh : Memo X 0 := (memo_corner h b).cross hv; have ht : Memo Y 0 := h.cross (memo_corner hv b)
  have hc : directionM (X+Y) 0 a=directionM X 0 a+directionM Y 0 a := by
    ext k l; exact (by rw [directionM,Matrix.of_apply]; simp only [Pi.add_apply,Matrix.add_apply, fderiv_fun_add ((hh _ _).differentiableAt (by simp)) ((ht _ _).differentiableAt (by simp)),_root_.add_apply]; rfl)
  rw [show (fun v => directionM U v b * W v + U v * directionM W v b)=X+Y from rfl,hc]; unfold X Y
  rw [direction_prod (memo_corner h b) hv,direction_prod h (memo_corner hv b),coins_M h,coins_M hv, add_assoc (_ + _) (_*_)]
end ledger
end YM.Stationary
end

/-!
# Reverse bars & log term. In Lorentz-independent coarse frequencies (complex amplitude only).
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} [Fintype ι] [DecidableEq ι]

lemma art_neighbor {U V : Corn ι → Matrix α β ℝ} (h : U =ᶠ[𝓝 0] V) (n) (u) : art U n u=art V n u := by
  ext i j; simp only [art,beat,Matrix.of_apply,show iteratedFDeriv ℝ n (fun z => U z i j) 0 = iteratedFDeriv ℝ n (fun z => V z i j) 0 from ((show (fun z => U z i j) =ᶠ[𝓝 0] fun z => V z i j from h.mono (by intro k hi; exact congr_fun (congr_fun hi i) j)).iteratedFDeriv ℝ n).eq_of_nhds]

variable [Fintype α] [DecidableEq α] {U V : Corn ι → Matrix α α ℝ}
lemma cash_safe {U : Corn ι → Matrix α α ℝ} (hx : IsUnit (U 0).det) : IsUnit (cardM U).det := by
  have hL : (approached (U 0)).det= ((U 0).det:ℂ) := (Complex.ofRealHom.map_det (U 0)).symm
  unfold cardM; rw [hL]; exact hx.map Complex.ofRealHom
lemma card_flip (he : IsUnit (U 0).det) : cardM (fun a => (U a)⁻¹)=(cardM U)⁻¹ := by
  have hM : cardM U*(cardM U)⁻¹=1 := mul_nonsing_inv _ (cash_safe he)
  have heq : cardM U * cardM (fun a => (U a)⁻¹)=1 := by
    unfold cardM; dsimp only; rw [← prom_mul,mul_nonsing_inv _ he]; ext i j; by_cases h : i=j <;> simp [approached, Matrix.one_apply, *]
  have hu := heq.trans hM.symm
  simpa only [Matrix.nonsing_inv_mul_cancel_left (cardM U) _ (cash_safe he)] using congr_arg ((cardM U)⁻¹ * ·) hu

lemma seat_flip (h : Memo U 0) (he : IsUnit (U 0).det) (u : Phase ι) :
    seat (fun a => (U a)⁻¹) u = -((cardM U)⁻¹*seat U u*(cardM U)⁻¹) := by
  refine Leads.buys (seat_e _) ((((seat_e U).lower _).upper _).neg) ?_ u
  intro z; simp only [seating,direction_inverse h he.ne_zero, ← card_flip he]
  change approached _ = - (approached (U 0)⁻¹ * approached _ * approached (U 0)⁻¹)
  rw [← prom_mul,← prom_mul]; ext; simp [approached]
lemma cart_flip (h : Memo U 0) (he : IsUnit (U 0).det) (u v : Phase ι) :
    let W : Corn ι →Matrix α α ℝ := fun a => (U a)⁻¹
    let P := (cardM U)⁻¹
    cart W u v= -((seat W v * seat U u + seat W u * seat U v + P * cart U u v) * P) := by
  intro W P
  have hW : Memo W 0 := h.flip he.ne_zero
  have hk : cart (fun a => W a * U a) u v=0 := Eq.trans
    (art_neighbor (U:=fun a => W a * U a) (V:=fun _ => 1) (by filter_upwards [h.det_val.continuousAt.eventually_ne he.ne_zero] with a ha; exact nonsing_inv_mul _ ha.isUnit) 2 ![u,v])
      (art_raw _ (by decide : 2≠0) _)
  rw [cart_prod hW h,show cardM W=P from card_flip he,add_assoc,add_assoc] at hk
  have hm := congr_arg (·*P) (eq_neg_of_add_eq_zero_left hk)
  simpa only [P, Matrix.mul_nonsing_inv_cancel_right _ _ (cash_safe he), neg_mul, add_assoc] using hm

omit [DecidableEq α] in
lemma trace_realized (U : Matrix α α ℝ) : (approached U).trace=(U.trace:ℂ) := by simp [approached,trace]

lemma trace_scrim (h : Memo U 0) (he : IsUnit (U 0).det) (p q : Phase ι) :
    let X := (cardM U)⁻¹
    beat (fun a => Real.log (U a).det) 0 2 ![p,q] = (X*cart U p q).trace -(((X*seat U p)*X)*seat U q).trace := by
  intro X
  refine Leads.two (left_beat _) (right_beat _)
    (fun i => (((cart_left U i).lower X).tab).sub (((((seat_e U).lower X).upper _).upper _).tab))
    (fun i => (((cart_right U i).lower X).tab).sub (((seat_e U).lower _).tab)) ?_ p q
  intro i j
  rw [show ![axes i,axes j]=axes ∘ (![i,j]:Fin 2 → _) by funext k; fin_cases k <;> rfl, beat_real, trace_log h _ _ he.ne_zero]
  rw [show X=approached ((U 0)⁻¹) from (card_flip he).symm,carting,seating,seating,
    ← prom_mul,← prom_mul, ← prom_mul, ← prom_mul, trace_realized,trace_realized,Complex.ofReal_sub]
end YM.Stationary
end

/-!
# Film: routed jets with two distinguished external momenta over every Co shape.

Separate amplitude TYPE indices here. More than enough by complex linearity
for external waves. Routing exact also if one of them alone doesn't occur.
Translations / convolution norm arguments will mostly be at flat with
several incoming this same shift, distinguish macros. Lega for analysts
independent of algebra. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} {m : Side}

structure Film (ι α β : Type) where
  tab : Momentum → CompM α β
  spot : ι → Momentum → Momentum → CompM α β
  -- `arch i j p q r`: insert (i,p) & (j,q); incoming r.
  arch : ι → ι → Momentum → Momentum → Momentum → CompM α β

namespace Film
def plus (F G : Film ι α β) : Film ι α β := ⟨F.tab+G.tab,F.spot+G.spot,F.arch+G.arch⟩
def weight (c : ℂ) (F : Film ι α β) : Film ι α β := ⟨c • F.tab,c • F.spot,c • F.arch⟩
def rear (F : Film ι α β) : Film ι β α := ⟨fun q => (F.tab (-q))ᵀ,
    fun i p q => (F.spot i p (-(q+p)))ᵀ, fun i j p q r => (F.arch i j p q (-(r+(p+q))))ᵀ⟩
def cardF (K : Momentum → CompM α β) : Film ι α β := ⟨K,0,0⟩

def pay [Fintype β] (F : Film ι α β) (G : Film ι β γ) : Film ι α γ where
  tab q := F.tab q * G.tab q
  spot i p q := F.spot i p q *G.tab q + F.tab (q+p)*G.spot i p q
  arch i j p q r := F.arch i j p q r*G.tab r + F.spot j q (r+p)*G.spot i p r + F.spot i p (r+q)*G.spot j q r +
      F.tab (r+(p+q))*G.arch i j p q r

variable [Fintype α] [DecidableEq α]

def coupon (F : Film ι α α) (q : Momentum) := (F.tab q)⁻¹
def vSpot (F : Film ι α α) (i : ι) (p q : Momentum) := -(F.coupon (q+p)*F.spot i p q*F.coupon q)
def back (F : Film ι α α) : Film ι α α where
  tab q := F.coupon q
  spot := F.vSpot
  arch i j p q r := -((F.vSpot j q (r+p)*F.spot i p r + F.vSpot i p (r+q)*F.spot j q r + F.coupon (r+(p+q))*F.arch i j p q r)*F.coupon r)
end Film

abbrev OperatorF (ι : Type) (m : Side) (α β : Type) := Corn (Co m ι) → Matrix (Co m α) (Co m β) ℝ
variable [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
structure Ticket (F : Film ι α β) (U : OperatorF ι m α β) : Prop where
  finance : Memo U 0
  tab : Jaunt (cardM U) F.tab 0
  spot (i : ι) (p : Site m) (q : Momentum) : rolls (mon p) q → Jaunt (seat U (relay p i)) (F.spot i q) p
  arch (i j : ι) (a b : Site m) (p q : Momentum) : rolls (mon a) p → rolls (mon b) q →
      Jaunt (cart U (relay a i) (relay b j)) (F.arch i j p q) (a+b)

namespace Ticket
variable {F P : Film ι α β} {U V : OperatorF ι m α β}

lemma current (F : Momentum →CompM α β) (U : Matrix (Co m α) (Co m β) ℝ) (he : Jaunt (approached U) F 0) : Ticket (Film.cardF (ι:=ι) F) (fun _ => U) := by
  refine ⟨Memo.raw U 0,he,fun i p q _ => ?_,fun i j p q u v _ _ => ?_⟩
  · unfold seat; rw [art_raw U one_ne_zero]; exact Jaunt.zero p
  unfold cart; rw [art_raw U (by decide)]; exact Jaunt.zero _

lemma plus (h : Ticket F U) (he : Ticket P V) : Ticket (F.plus P) (U+V) := by
  refine ⟨h.finance.twice he.finance,?_,fun i p q hx => ?_,fun i j p q r s hp hq => ?_⟩
  · rw [cardM,Pi.add_apply,prom_addition]; exact h.tab.plus he.tab
  · unfold seat; rw [art_plus h.finance he.finance]; exact (h.spot i p q hx).plus (he.spot i p q hx)
  unfold cart; rw [art_plus h.finance he.finance]; exact (h.arch i j p q r s hp hq).plus (he.arch i j p q r s hp hq)
lemma weight (h : Ticket F U) (c : ℝ) : Ticket (F.weight c) (c • U) := by
  refine ⟨h.finance.debit c, ?_,fun i p q hp => ?_, fun i j p q r s hp hq => ?_⟩
  · rw [cardM,Pi.smul_apply,prom_tone]; exact h.tab.smul _
  · unfold seat; rw [art_smul c h.finance]; exact (h.spot i p q hp).smul _
  unfold cart; rw [art_smul c h.finance]; exact (h.arch i j p q r s hp hq).smul _
lemma rear (h : Ticket F U) : Ticket F.rear (fun z => (U z)ᵀ) := by
  have ht : rolls (Bloch.mon (0:Site m)) 0 := by rw [mon_zero]; exact rolls.refl _
  have he := h.tab.adjoin ht
  simp only [add_zero] at he
  exact ⟨h.finance.spot,he,fun i p q hp => (h.spot i p q hp).adjoin hp,
    fun i j p q r s hp hq => (h.arch i j p q r s hp hq).adjoin (hp.combine hq)⟩
lemma Jaunt0 {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {P : CircM m α β} {V : CircM m β γ} {p : Site m} {f : Momentum→CompM α β} {g : Momentum→CompM β γ} (h : Jaunt P f p) (hv : Jaunt V g 0) :
    Jaunt (P*V) (fun i => f i*g i) p := by
  have ht : rolls (mon (0:Site m)) 0 := by rw [mon_zero]; exact rolls.refl _
  simpa using h.join hv ht (zero_add p)
lemma pay (h : Ticket F U) [Fintype γ] [DecidableEq γ] {G : Film ι β γ} {V : OperatorF ι m β γ} (he : Ticket G V) : Ticket (F.pay G) (fun z => U z*V z) := by
  refine ⟨h.finance.cross he.finance,?_,fun i p q hp => ?_,fun i j a b p q ha hb => ?_⟩
  · rw [show cardM (fun z => U z * V z)=cardM U * cardM V from prom_mul ..]; exact Jaunt0 h.tab he.tab
  · rw [seat_prod h.finance he.finance]
    exact (Jaunt0 (h.spot i p q hp) he.tab).plus (h.tab.join (he.spot i p q hp) hp (add_zero _))
  rw [cart_prod h.finance he.finance]
  exact (((Jaunt0 (h.arch i j a b p q ha hb) he.tab).plus ((h.spot j b q hb).join (he.spot i a p ha) ha rfl)).plus
    ((h.spot i a p ha).join (he.spot j b q hb) hb (add_comm b a))).plus (h.tab.join (he.arch i j a b p q ha hb) (ha.combine hb) (add_zero _))

variable {W : OperatorF ι m α α} {K : Film ι α α}
lemma back (h : Ticket K W) (he : IsUnit (W 0).det) : Ticket K.back (fun z => (W z)⁻¹) := by
  let X := fun z => (W z)⁻¹
  let M := (cardM W)⁻¹
  have ht : Jaunt M K.coupon 0 := h.tab.backway (cash_safe he)
  have hx (i) (p : Site m) (q) (hp : rolls (mon p) q) : Jaunt (seat X (relay p i)) (K.vSpot i q) p := by
    unfold X; rw [seat_flip h.finance he]; exact (Jaunt0 (ht.join (h.spot i p q hp) hp (add_zero p)) ht).backside
  refine ⟨Memo.flip h.finance he.ne_zero,?_,hx,fun i j a b p q hp hq => ?_⟩
  · rw [card_flip he]; exact ht
  have hh : cart X (relay a i) (relay b j)=_ := cart_flip h.finance he (relay a i) (relay b j)
  rw [show (fun z => (W z)⁻¹)=X from rfl,hh]
  exact (Jaunt0 ((((hx j b q hq).join (h.spot i a p hp) hp rfl).plus ((hx i a p hp).join (h.spot j b q hq) hq (add_comm b a))).plus
    (ht.join (h.arch i j a b p q hp hq) (hp.combine hq) (add_zero _))) ht).backside
end Ticket
end YM.Stationary
end

/-!
# Routed complex domain.

Choose all subset momenta of an arc trajectory simultaneously in strip,
including individual external momentum. Closed under vertical composition
and TRANSPOSE from outgoing dual. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} {m : Side} {q p r : Momentum} {σ A η : ℝ}

/-- one insertion p on momentum q. -/
structure Avenue (σ : ℝ) (p q : Momentum) : Prop where
  side : p ∈ strip σ
  basic : q ∈ strip σ
  added : q+p ∈ strip σ

structure Boulevard (σ : ℝ) (p q r : Momentum) : Prop where
  oneWay : Avenue σ p r
  second : Avenue σ q r
  total : r+(p+q) ∈ strip σ

lemma Avenue.part (h : Avenue σ p q) (he : σ≤η) : Avenue η p q :=
    ⟨fun i => (h.side i).trans_le he, fun i => (h.basic i).trans_le he, fun i => (h.added i).trans_le he⟩
lemma Avenue.late (h : Avenue σ p q) : Avenue σ p (-(q+p)) := by
  refine ⟨h.side, fun i => ?_, fun i => ?_⟩
  · simp only [Pi.neg_apply,Complex.neg_im,abs_neg]; exact h.added i
  rw [neg_add_rev, add_right_comm, neg_add_cancel,zero_add]; simpa using! h.basic i

namespace Boulevard
variable (h : Boulevard σ p q r)
include h
lemma costs (he : σ≤η) : Boulevard η p q r := ⟨h.oneWay.part he,h.second.part he, fun i => (h.total i).trans_le he⟩
lemma proceed : Avenue σ p (r+q) := ⟨h.oneWay.side,h.second.added,by rw [add_right_comm,add_assoc]; exact h.total⟩
lemma roads : Avenue σ q (r+p) := ⟨h.second.side,h.oneWay.added,by rw [add_assoc]; exact h.total⟩
lemma ebb : Boulevard σ p q (-(r+(p+q))) := by
  constructor
  · rw [← add_assoc, add_right_comm]; exact h.proceed.late
  · rw [← add_assoc]; exact h.roads.late
  intro i; rw [neg_add_rev, add_right_comm, neg_add_cancel,zero_add]; simpa using h.oneWay.basic i
end Boulevard

/-- Entry differentiability. -/
abbrev BillD {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (F : X → Matrix α β ℂ) (x : X) := ∀ i j,DifferentiableAt ℂ (fun z => F z i j) x

namespace BillD
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {x : X} {U V : X → Matrix α β ℂ}
lemma park (x : X) (V : Matrix α β ℂ) : BillD (fun _ => V) x := fun _ _ => differentiableAt_const _
lemma bond [Fintype β] {W : X→ Matrix β γ ℂ} (h : BillD U x) (he : BillD W x) : BillD (fun z => U z*W z) x := by
  intro i j; simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (h i k).mul (he k j)
lemma plus (h : BillD U x) (he : BillD V x) : BillD (fun i => U i + V i) x := fun i j => (h i j).add (he i j)
lemma less (h : BillD U x) (he : BillD V x) : BillD (fun i => U i - V i) x := fun i j => (h i j).sub (he i j)
lemma neg (h : BillD U x) : BillD (fun i => -U i) x := fun i j => (h i j).neg
lemma debit (c : ℂ) (h : BillD U x) : BillD (c • U) x := fun i j => (h i j).const_smul c
lemma spot (h : BillD U x) : BillD (fun z => (U z)ᵀ) x := fun i j => h j i
lemma enter {f : X→Y} {F : Y→ Matrix α β ℂ} (h : BillD F (f x)) (he : DifferentiableAt ℂ f x) : BillD (fun z => F (f z)) x := fun i j => (h i j).comp _ he

variable [Fintype α] [DecidableEq α] {P : X→Matrix α α ℂ} (hp : BillD P x)
include hp
lemma via_det : DifferentiableAt ℂ (fun z => (P z).det) x := by
  simp only [Matrix.det_apply]
  refine DifferentiableAt.fun_sum fun i _ => ?_
  simp only [Units.smul_def,zsmul_eq_mul]; refine DifferentiableAt.mul (differentiableAt_const _) ?_
  suffices ht : ∀ S : Finset α,DifferentiableAt ℂ (fun z => ∏ j∈S,P z (i j) j) x from ht univ
  intro S; induction S using Finset.induction with
  | empty => simp
  | insert a l he IH => simp_rw [Finset.prod_insert he]; exact (hp _ _).mul IH
lemma take (h : IsUnit (P x).det) : BillD (fun z => (P z)⁻¹) x := by
  intro i j; simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply]
  refine ((hp.via_det.inv h.ne_zero).smul ?_)
  simp_rw [Matrix.adjugate_apply]; apply BillD.via_det
  intro k l; simp only [Matrix.updateRow_apply]; split; exact differentiableAt_const _
  exact hp _ _
lemma collects : DifferentiableAt ℂ (fun z => (P z).trace) x := DifferentiableAt.fun_sum fun i _ => hp i i
end BillD

structure Poster (σ : ℝ) (f : Momentum→CompM α β) : Prop where
  shape {p : Momentum} (h : p∈strip σ) : BillD f p
  shifts {p q : Momentum} (h : rolls p q) : p∈strip σ → f p=f q
structure Barter (σ : ℝ) (f : Momentum→Momentum→CompM α β) : Prop where
  shape {p q : Momentum} : Avenue σ p q → BillD (uncurry f) (p,q)
  shifts {p p' q q' : Momentum} (h : rolls p p') (he : rolls q q') : Avenue σ p q → f p q=f p' q'
abbrev road3 {X : Type} (f : Momentum → Momentum → Momentum → X) (p : Momentum × Momentum × Momentum) := f p.1 p.2.1 p.2.2
structure Stagehand (σ : ℝ) (f : Momentum→Momentum→Momentum→CompM α β) : Prop where
  shape {p q r : Momentum} : Boulevard σ p q r → BillD (road3 f) (p,q,r)
  shifts {p p' q q' r r' : Momentum} (h : rolls p p') (he : rolls q q') (hv : rolls r r') : Boulevard σ p q r → f p q r=f p' q' r'

structure Play (F : Film ι α β) (σ : ℝ) : Prop where
  tab : Poster σ F.tab
  spot i : Barter σ (F.spot i)
  arch i j : Stagehand σ (F.arch i j)

namespace Play
variable {F P : Film ι α β}
lemma mono (h : Play F σ) (hp : η≤σ) : Play F η :=
  ⟨⟨fun w => h.tab.shape (fun j => (w j).trans_le hp),fun he w => h.tab.shifts he (fun j => (w j).trans_le hp)⟩,
   fun i => ⟨fun w => (h.spot i).shape (w.part hp),fun h1 h2 w => (h.spot i).shifts h1 h2 (w.part hp)⟩,
   fun i j => ⟨fun w => (h.arch i j).shape (w.costs hp),fun h1 h2 h3 w => (h.arch i j).shifts h1 h2 h3 (w.costs hp)⟩⟩
lemma current {K : Momentum → CompM α β} (h : Poster σ K) : Play (Film.cardF (ι:=ι) K) σ :=
    ⟨h,fun _ => ⟨fun _ => BillD.park _ 0,fun _ _ _ => rfl⟩,fun _ _ => ⟨fun _ => BillD.park _ 0,fun _ _ _ _ => rfl⟩⟩
lemma plus (h : Play F σ) (hp : Play P σ) : Play (F.plus P) σ :=
    ⟨⟨fun e => (h.tab.shape e).plus (hp.tab.shape e),fun he w => congr_arg₂ (·+·) (h.tab.shifts he w) (hp.tab.shifts he w)⟩,
     fun i => ⟨fun e => BillD.plus ((h.spot i).shape e) ((hp.spot i).shape e),fun he ha w => congr_arg₂ (·+·) ((h.spot i).shifts he ha w) ((hp.spot i).shifts he ha w)⟩,
     fun i j => ⟨fun e => BillD.plus ((h.arch i j).shape e) ((hp.arch i j).shape e),fun he ha hb w => congr_arg₂ (·+·) ((h.arch i j).shifts he ha hb w) ((hp.arch i j).shifts he ha hb w)⟩⟩
lemma weight (h : Play F σ) (c : ℂ) : Play (F.weight c) σ :=
    ⟨⟨fun e => (h.tab.shape e).debit c,fun he w => congr_arg (c • ·) (h.tab.shifts he w)⟩,
     fun i => ⟨fun e => BillD.debit c ((h.spot i).shape e),fun he ha w => congr_arg (c • ·) ((h.spot i).shifts he ha w)⟩,
     fun i j => ⟨fun e => BillD.debit c ((h.arch i j).shape e),fun he ha hb w => congr_arg (c • ·) ((h.arch i j).shifts he ha hb w)⟩⟩
end Play
end YM.Stationary
end

/-! # strip analyticity book & trace evaluation ANY mesh. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β γ : Type} {m : Side} {q p r : Momentum} {σ A : ℝ}
section transport
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {x : X} {p q r : X → Momentum}
lemma Poster.go {K : Momentum → CompM α β} (h : Poster σ K) (he : p x∈strip σ) (hp : DifferentiableAt ℂ p x) : BillD (fun v => K (p v)) x := BillD.enter (h.shape he) hp
lemma Barter.go {K : Momentum→Momentum→CompM α β} (h : Barter σ K) (w : Avenue σ (p x) (q x))
    (hp : DifferentiableAt ℂ p x) (hq : DifferentiableAt ℂ q x) : BillD (fun v => K (p v) (q v)) x := BillD.enter (f:=fun x => (p x,q x)) (h.shape w) (hp.prodMk hq)
lemma Stagehand.go {K : Momentum→Momentum→Momentum→CompM α β} (h : Stagehand σ K) (w : Boulevard σ (p x) (q x) (r x))
    (hp : DifferentiableAt ℂ p x) (hq : DifferentiableAt ℂ q x) (hr : DifferentiableAt ℂ r x) : BillD (fun v => K (p v) (q v) (r v)) x := BillD.enter (f:=fun x => (p x,q x,r x)) (h.shape w) (hp.prodMk (hq.prodMk hr))
end transport

namespace Play
variable {F : Film ι α β} {P : Film ι β γ}
lemma rear (h : Play F σ) : Play F.rear σ := by
  refine ⟨⟨fun hp => ?_,fun h1 w => ?_⟩,fun i => ⟨fun he => ?_,fun h1 h2 w => ?_⟩,fun i j => ⟨fun he => ?_,fun h1 h2 h3 w => ?_⟩⟩
  · rename_i p; have hy : -p∈ strip σ := fun j => by simpa using! hp j
    exact BillD.spot (h.tab.go (p:=fun z => -z) hy (by fun_prop))
  · exact congr_arg transpose (h.tab.shifts h1.neg (fun i => by simpa using w i))
  · exact BillD.spot ((h.spot i).go (p:=Prod.fst) (q:=fun a : Momentum × Momentum => -(a.2+a.1)) he.late (by fun_prop) (by fun_prop))
  · exact congr_arg transpose ((h.spot i).shifts h1 (h2.plus h1).neg w.late)
  · exact BillD.spot ((h.arch i j).go (p:=Prod.fst) (q:=fun a : Momentum×Momentum×Momentum => a.2.1) (r:=fun a : Momentum× Momentum × Momentum => -(a.2.2+(a.1+a.2.1))) he.ebb (by fun_prop) (by fun_prop) (by fun_prop))
  exact congr_arg transpose ((h.arch i j).shifts h1 h2 (h3.plus (h1.plus h2)).neg w.ebb)
lemma pay [Fintype β] (h : Play F σ) (hp : Play P σ) : Play (F.pay P) σ := by
  refine ⟨⟨fun w => BillD.bond (h.tab.shape w) (hp.tab.shape w),fun he w => ?_⟩, fun i => ⟨fun w => ?_,fun h1 h2 w => ?_⟩,
    fun i j => ⟨fun w => ?_,fun h1 h2 h3 w => ?_⟩⟩
  · simp only [Film.pay,h.tab.shifts he w,hp.tab.shifts he w]
  · rename_i p q
    have he := hp.tab.go (p:=Prod.snd) (x:=(p,q)) w.basic (by fun_prop)
    have hw := h.tab.go (p:=fun a : Momentum × Momentum => a.2+a.1) (x:=(p,q)) w.added (by fun_prop)
    exact BillD.plus (BillD.bond ((h.spot i).shape w) he) (BillD.bond hw ((hp.spot i).shape w))
  · simp only [Film.pay, (hp.spot i).shifts h1 h2 w, (h.spot i).shifts h1 h2 w, h.tab.shifts (h2.plus h1) w.added, hp.tab.shifts h2 w.basic]
  · rename_i p q r
    let z := (p,q,r)
    let X := Momentum × Momentum × Momentum
    let f : X → Momentum := Prod.fst; let g : X→ Momentum := fun a => a.2.1; let m : X → Momentum := fun a => a.2.2
    have hf : DifferentiableAt ℂ f z := differentiableAt_fst
    have hg : DifferentiableAt ℂ g z := differentiableAt_fst.comp z differentiableAt_snd
    have hm : DifferentiableAt ℂ m z := differentiableAt_snd.comp z differentiableAt_snd
    have H := hp.tab.go w.oneWay.basic hm
    have hl := h.tab.go (x:=z) w.total (hm.add (hf.add hg))
    have h₁ := (hp.spot i).go w.oneWay hf hm; have h₂ := (hp.spot j).go w.second hg hm
    have h₃ := (h.spot j).go w.roads hg (hm.add hf); have h₄ := (h.spot i).go w.proceed hf (hm.add hg)
    exact ((((BillD.bond ((h.arch i j).shape w) H).plus (h₃.bond h₁)).plus (h₄.bond h₂)).plus (hl.bond ((hp.arch i j).shape w)))
  simp only [Film.pay,(hp.arch i j).shifts h1 h2 h3 w, (h.arch i j).shifts h1 h2 h3 w, (hp.spot i).shifts h1 h3 w.oneWay,(hp.spot j).shifts h2 h3 w.second, (h.spot j).shifts h2 (h3.plus h1) w.roads,(h.spot i).shifts h1 (h3.plus h2) w.proceed,h.tab.shifts (h3.plus (h1.plus h2)) w.total,hp.tab.shifts h3 w.oneWay.basic]

variable [Fintype α] [DecidableEq α] {K : Film ι α α}
lemma back (h : Play K σ) (he : ∀ p ∈ strip σ, IsUnit (K.tab p).det) : Play K.back σ := by
  have hk : Poster σ K.coupon := ⟨fun w => BillD.take (h.tab.shape w) (he _ w),fun he w => congr_arg (·⁻¹) (h.tab.shifts he w)⟩
  have hx (i) : Barter σ (K.vSpot i) := by
    refine ⟨fun w => ?_,fun h1 h2 w => ?_⟩
    · rename_i p q
      exact BillD.neg (BillD.bond (BillD.bond (hk.go (p:=fun p : Momentum × Momentum => p.2+p.1) (x:=(p,q)) w.added (by fun_prop)) ((h.spot i).shape w)) (hk.go (p:=Prod.snd) (x:=(p,q)) w.basic (by fun_prop)))
    simp only [Film.vSpot,hk.shifts h2 w.basic,hk.shifts (h2.plus h1) w.added,(h.spot i).shifts h1 h2 w]
  refine ⟨hk,hx,fun i j => ⟨fun w => ?_,fun h1 h2 h3 w => ?_⟩⟩
  · rename_i p q r
    let z := (p,q,r)
    let X := Momentum × Momentum × Momentum
    let f : X → Momentum := Prod.fst; let g : X→ Momentum := fun a => a.2.1; let m : X → Momentum := fun a => a.2.2
    have hf : DifferentiableAt ℂ f z := differentiableAt_fst
    have hg : DifferentiableAt ℂ g z := differentiableAt_fst.comp z differentiableAt_snd
    have hm : DifferentiableAt ℂ m z := differentiableAt_snd.comp z differentiableAt_snd
    have h₁ := (h.spot i).go w.oneWay hf hm; have h₂ := (h.spot j).go w.second hg hm
    have h₃ := (hx j).go w.roads hg (hm.add hf); have h₄ := (hx i).go w.proceed hf (hm.add hg)
    have H := hk.go (x:=z) w.total (hm.add (hf.add hg))
    exact BillD.neg ((((h₃.bond h₁).plus (h₄.bond h₂)).plus (H.bond ((h.arch i j).shape w))).bond (hk.go w.oneWay.basic hm))
  simp only [Film.back, (h.arch i j).shifts h1 h2 h3 w, (h.spot i).shifts h1 h3 w.oneWay,(h.spot j).shifts h2 h3 w.second,(hx i).shifts h1 (h3.plus h2) w.proceed,(hx j).shifts h2 (h3.plus h1) w.roads,hk.shifts (h3.plus (h1.plus h2)) w.total,hk.shifts h3 w.oneWay.basic]
end Play
end YM.Stationary
end

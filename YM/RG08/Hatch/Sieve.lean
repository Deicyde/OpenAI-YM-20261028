import YM.RG08.Hatch.Reed

/-!
# cofinal single response kernels, incl winding & scalar.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Hatch
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets
open scoped Topology BigOperators ENNReal Classical
variable {I J:Type}[Fintype I][Fintype J]{n m d:ℕ}{σ C B Y:ℝ}{h:0<σ}
variable {P:Pack (m+1) (Market I)}{Q:Span (m+1) I}{γ:Forms.Line (Market I)}{Γ:(i:ℕ)→Forms.Line (colony I i)}

omit [Fintype I] in
private lemma dues (hp:Reed d h C P Q)(f:Pearl)(hg:StudyLine σ B Γ γ)(i:ℕ)(x:Tape m (colony I i))(u v:colony I i): |Γ i u v| * |Q i (Fin.cons u x) f|≤ B*(C*beam d h f) * (weightU (σ/2) (reach u)*weightU (σ/2) (reach v)):=by
 let z:= (Fin.cons u x:Tape (m+1) _); let c:=crest (chain i) I; let D:=shore (chain i) I
 have hv:|Q i z f|≤ C * beam d h f* Real.exp (-σ*native u):=(Hatch.decay c (hp.openQ i) (hp.back i) hp.cost f z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by simpa only [z,Fin.cons_zero] using (show native (z 0)≤c.cage z from c.float z 0)) (by linarith only [h]))) (mul_nonneg hp.cost (beam_nn ..)))
 apply (mul_le_mul (hg.point i u v) hv (abs_nonneg _) (by have :=hg.palm.gain;positivity)).trans
 unfold weightU;rw [here,here,←Real.exp_add]
 calc
 _ = B*(C*beam d h f) * Real.exp (-σ*((D).span u v) + (-σ*native u)):=by rw [Real.exp_add];ring
 _ ≤ _ := by
     apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hg.palm.gain (mul_nonneg hp.cost (beam_nn ..)))
     have he:native v ≤D.span u v+native u:=by rw [←D.left];exact region v u
     have ht:=D.nn u v
     nlinarith only [he,ht,h]

lemma Reed.squeak {P:Pack (n+2) (Market I)}{Q:Span (n+2) I}(hp:Reed d h C P Q)(hg:StudyLine σ B Γ γ):Reed d h (C*B) (pocket γ P) (fun i=>pocket (Γ i) (Q i)):=by
 unfold pocket; apply Reed.symm
 have he:=looted (F:=P) hg.palm hp.lead
 have hf i:= looted (hg.calm i) (hp.back i)
 refine ⟨mul_nonneg hp.cost hg.palm.gain,he.lyric (seed hp.openP),fun i=>(hf i).lyric (seed (hp.openQ i)),he.sings,fun i=>(hf i).sings,fun f z=>?_⟩
 let r:= (carpetRoad I).prod (carpetRoad I)
 let A:= B*(C*beam d h f)
 unfold decker nut;simp only [Pi.smul_apply,smul_eq_mul]
 have ha:0≤A:=mul_nonneg hg.palm.gain (mul_nonneg hp.cost (beam_nn ..))
 refine DCT r (fun i u=>Γ i u.1 u.2*Q i (Fin.cons u.1 (Fin.cons u.2 (port (chain i) ∘ z))) f) (fun u=>γ u.1 u.2* P (Fin.cons u.1 (Fin.cons u.2 z)) f) (fun u=>A*(weightU (σ/2) u.1*weightU (σ/2) u.2)) ?_ ((weightU_twice (by linarith only [h])).mul_left A) (fun u=>by unfold weightU;positivity) (.of_forall fun i ⟨u,v⟩=>?_)
 · intro u
   refine Tendsto.mul (hg.light u.1 u.2) ?_
   convert hp.front f (Fin.cons u.1 (Fin.cons u.2 z)) using 2
   dsimp only [r,Route.prod,carpetRoad]; congr 2;ext j:1;cases j using Fin.cases with
   | zero=>rfl
   | succ j=>cases j using Fin.cases<;> rfl
 rw [Real.norm_eq_abs,abs_mul];exact dues hp f hg i _ u v

lemma Reed.chalk {F:Forms.Flake (n+1) (Market I)}{v:ViewDeck (n+1) I}(hp:Reed d h C P Q)(hg:StudyLine σ B Γ γ)(he:Study σ Y v F) : Reed d h (C*B*Y) (cloak γ P F) (fun i=>cloak (Γ i) (Q i) (v i)):=by
 unfold cloak; apply Reed.symm
 have hu:=jackets (spindled I) hp.lead he.palm hg.palm hp.cost
 have hw i:= jackets (crested _ I) (hp.back i) (he.calm i) (hg.calm i) hp.cost
 refine ⟨mul_nonneg (mul_nonneg hp.cost hg.palm.gain) he.cost,hu.lyric (cuff hp.openP),fun i=>(hw i).lyric (cuff (hp.openQ i)),hu.sings,fun i=>(hw i).sings,fun f z=>?_⟩
 let r:= (carpetRoad I).prod (carpetRoad I)
 let A:= B*(C*beam d h f);have ha:0≤A:=mul_nonneg hg.palm.gain (mul_nonneg hp.cost (beam_nn ..))
 let X(z:Tape (m+n) (Market I)):Tape m (Market I):=fun i => z (Fin.castAdd n i)
 let U(z:Tape (m+n) (Market I)):Tape n (Market I):=fun i=> z (Fin.natAdd m i)
 let φ(i:ℕ):= port (chain i) (I:=I)
 let ψ(Z:Type) (γ:Forms.Line Z)(F:Flake (n+1) Z)(P:Pack (m+1) Z)(u:Tape n Z)(x:Tape m Z)(ab:Z×Z):=γ ab.1 ab.2* F (Fin.cons ab.2 u) *P (Fin.cons ab.1 x) f
 refine DCT r (fun i=>ψ _ (Γ i) (v i) (Q i) (φ i ∘ U z) (φ i ∘ X z)) (ψ _ γ F P (U z) (X z)) (fun u=>(A*Y)*(weightU (σ/2) u.1*weightU (σ/2) u.2)) ?_ ((weightU_twice (by linarith only [h])).mul_left (A*Y)) (fun u=>by unfold weightU;have ht:=he.cost;positivity) (.of_forall fun i ⟨a,b⟩=>?_)
 · rintro ⟨a,b⟩; unfold ψ
   refine Tendsto.mul (Tendsto.mul (hg.light a b) ?_) ?_
   · convert he.light (by omega) (Fin.cons b (U z)) using 2
     congr 2;ext j:1;cases j using Fin.cases<;> rfl
   convert hp.front f (Fin.cons a (X z)) using 2; dsimp only [r,Route.prod,carpetRoad,φ]; congr 2;ext j:1;cases j using Fin.cases <;> rfl
 unfold ψ;rw [Real.norm_eq_abs,abs_mul,abs_mul,mul_right_comm];dsimp only [r,Route.prod,carpetRoad]
 apply (mul_le_mul (dues hp f hg i _ a b) ((he.calm i).plain he.cost he.rate.le (by omega) _) (abs_nonneg _) (by have :=ha; unfold weightU A at *;positivity)).trans_eq
 unfold A;ring

omit [Fintype I][Fintype J] in
private lemma home_cross {K:Kernel I J}{q:(i:ℕ)→colony I i→colony J i→ℝ}(hr:StudyCross I J σ Y q K)(n:ℕ):
  let E:Cables n (Market I) (Market J):=fun _ x y=>σ*sep x.1 y.1
  ; Parade (stance I) (stance J) σ E (fun _=>K) (fun _=>Y) ∧ ∀ i,Parade (crest (chain i) I) (crest (chain i) J) σ (n:=n) (fun _ x y=>σ*Isles.walk (P:=chain i) x.1 y.1) (fun _=>q i) (fun _=>Y):=by
 intro E
 constructor
 · refine ⟨fun _ x y _=> ?_,fun _ x y=>mul_nonneg hr.rate.le (sep_nonneg ..), fun _=>hr.cost, fun _=>hr.near⟩
   let u:Market J:=(x.1,y.2); have he:=spindled J u y
   unfold E; rw [←mul_add];exact mul_le_mul_of_nonneg_left he hr.rate.le
 intro i; refine ⟨fun _ x y _=> ?_, fun _ x y=>mul_nonneg hr.rate.le (by unfold Isles.walk;positivity),fun _=>hr.cost,fun _=>hr.low i⟩
 let u:colony J i:=(x.1,y.2);have he:=crested (chain i) J u y
 rw [←mul_add];exact mul_le_mul_of_nonneg_left he hr.rate.le

omit [Fintype J] in
lemma Reed.rafts {K:Kernel I J}{q:(i:ℕ)→colony I i→colony J i→ℝ}{e:ℕ}{P:GrainS (Market I)}{Q:(i:ℕ)→GrainS (colony I i)}(hp:Reed d h C (P e n) (fun i=>Q i e n))(hr:StudyCross I J σ Y q K): Reed d h (C*Y^n) (Trickle.mouth K P e n) (fun i=>Trickle.mouth (q i) (Q i) e n):=by
 obtain ⟨ht,hx⟩:=home_cross hr n; have he := (Parade.play (h:=h) (k:=h) ht le_rfl (le_rfl:d≤d));have hf(i):=(Parade.play (h:=h) (k:=h) (hx i) le_rfl (le_rfl:d≤d))
 simp_rw [prod_const,card_univ,Fintype.card_fin] at he hf
 have hs:=playing hp.openP hp.lead he;have hg i:=playing (hp.openQ i) (hp.back i) (hf i)
 refine ⟨mul_nonneg hp.cost (pow_nonneg hr.cost _),hs.1,fun i=>(hg i).1,hs.2,fun i=>(hg i).2,fun f z=>?_⟩
 let φ(k:ℕ)(J:Type):= port (chain k) (I:=J)
 let A(i:Fin n):=Y*Real.exp (σ*Isles.abroad (z i));have ha(i):0≤A i:=mul_nonneg hr.cost (Real.exp_pos _).le
 let H:=C*beam d h f; have hh:0≤H:=mul_nonneg hp.cost (beam_nn ..)
 unfold Trickle.mouth picture decker reel audio candles design Steam.repeatLine; simp only [Pi.smul_apply,smul_eq_mul,Function.comp_apply]
 refine DCT ((carpetRoad I).cards n) (fun k x=> (∏ i,q k (x i) (φ k J (z i)))*Q k e n x f) _ (fun x=>(∏ i,A i)*H*(∏ i,weightU σ (x i))) (fun x=>Tendsto.mul ?_ (hp.front f x)) ((cards_price h).mul_left _) (fun u=>by apply mul_nonneg (mul_nonneg (prod_nonneg (fun i _=>ha i)) hh) (prod_nonneg (fun _ _=>(Real.exp_pos _).le))) (.of_forall fun i x=>?_)
 · exact tendsto_finsetProd _ fun i _=>hr.light ..
 rw [Real.norm_eq_abs,abs_mul,Finset.abs_prod,mul_right_comm _ H,←Finset.prod_mul_distrib]
 apply mul_le_mul (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun j _=>hr.point i (x j) (z j))) ((hp.back i).quote (hp.openQ i) hp.cost x f) (abs_nonneg _) (Finset.prod_nonneg (fun j _=>mul_nonneg (ha j) (Real.exp_pos _).le))
end YM.RG08.Hatch

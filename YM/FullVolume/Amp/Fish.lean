import YM.FullVolume.Amp.Drill
/-! Homogeneous polynomial along the coupon shell. No polarization in infinite directions assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Often
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y I : Type*} [DecidableEq I][SeminormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable (s:Finset I)(u:I→X){f:X→Y}{x:X}{c p r k:ℝ}{n j:ℕ}{P:ℕ→Y}{B:ℝ→Y}
variable (L : Often p f x r c)
include L
-- Tip via any scaling
lemma light {v:ℝ} (u:X) (hv:0<v) (he:‖v⁻¹ • u‖ ≤r): ∃ P:ℕ→Y,Tip (fun i => (v/p)^i • P i) (fun t:ℝ=> f (x+t • u)) ∧ SumBudget (fun i=> ‖P i‖) c ∧ ∀ t:ℝ,|v*t| ≤1 → HasSum (fun i:ℕ=> (v*t/p)^i • P i) (f (x+t • u)):=by
  obtain ⟨P,h,hp⟩:= L.looking _ he|>.scored
  have hh(t:ℝ)(ht:|v*t| ≤1): HasSum (fun i:ℕ=> (v*t/p)^i • P i) (f (x+t • u)):= by
    rw [show t • u=(v*t) • v⁻¹ • u from (by rw [smul_smul,show v*t*v⁻¹=t from (by field_simp)])]; exact hp _ (abs_le.mp ht)
  refine ⟨P,signpost (v/p) h ?_,h,hh⟩
  exact (sprite v).mono fun t ht=> by rw [show v/p*t=v*t/p from (by ring)]; exact hh t ht
lemma tubing (u:X) : ∃ B:ℕ→Y, Tip B (fun t:ℝ=> f (x+t • u)) := by
   let b:ℝ:= (‖u‖+1)/r; have hu:0<r:= L.width; have hb:0<b:=by unfold b; positivity
   let y: X:= b⁻¹ • u; have hV: ‖y‖≤ r:= by
     unfold y; rw [norm_smul,norm_inv,Real.norm_of_nonneg hb.le, inv_mul_le_iff₀ hb]; unfold b; rw [div_mul_cancel₀ _ hu.ne']; linarith
   exact ⟨_, (L.light u hb hV).choose_spec.1⟩
def bank (n:ℕ) (u:X):Y := (L.tubing u).choose n
lemma jump (u:X) : Tip (fun n=>L.bank n u) (fun t:ℝ=>f (x+t • u)):= (L.tubing u).choose_spec
lemma lend (i:ℕ)(u:X)(v:ℝ)(hv:0<v)(he:‖v⁻¹ • u‖≤ r): ‖L.bank i u‖≤ (v/p)^i*c:=by
   obtain ⟨P,hp,h,_⟩:= L.light u hv he
   have hh: L.bank i u=(v/p)^i • P i:= congr_fun (sole (L.jump u) hp) i; rw [hh,norm_smul,norm_pow,Real.norm_of_nonneg (by have hc:=L.pays.1; positivity : 0≤ v/p)]; apply mul_le_mul_of_nonneg_left (budget_single h i); have hc:=L.pays.1; positivity
lemma gift (u:X)(he:‖u‖ ≤ r): HasSum (fun i=>L.bank i u) (f (x+u)):=by
   obtain ⟨P,hp,_,h⟩:= L.light u zero_lt_one (show ‖(1:ℝ)⁻¹ • u‖≤r by simpa using he)
   rw [sole (L.jump u) hp]; simpa using h 1 (by norm_num)
lemma lend' (i:ℕ)(u:X)(v:ℝ)(hv:‖u‖≤r*v): ‖L.bank i u‖≤ (v/p)^i*c:=by
  have hh:= (Continuous.tendsto (show Continuous fun a:ℝ => (a/p)^i*c by fun_prop) v).mono_left (show 𝓝[>] v ≤ 𝓝 v from nhdsWithin_le_nhds)
  apply ge_of_tendsto hh
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ht:= L.width; have hu:= nonneg_of_mul_nonneg_right ((norm_nonneg _).trans hv) ht
  exact lend L _ u _ (hu.trans_lt (show v<a from ha)) (by rw [norm_smul,norm_inv,Real.norm_of_nonneg (hu.trans (le_of_lt (show v<a from ha))),inv_mul_le_iff₀ (hu.trans_lt (show v<a from ha))]; nlinarith [show v<a from ha])
lemma homo (a:ℝ) (u:X) (n:ℕ): L.bank n (a • u)= a^n • L.bank n u:=by
   apply congr_fun (f:=fun n=>L.bank n (a • u)) (g:=fun n=> a^n • L.bank n u) (sole (L.jump _) ?_) n
   intro n; have he: (fun t:ℝ=>t*a)=(fun t=>t*a):=rfl
   have ht : Tendsto (fun t:ℝ=>t*a) (𝓝 0) (𝓝 0):= by simpa using! Continuous.tendsto (show Continuous fun t:ℝ=>t*a by fun_prop) 0
   refine (( (L.jump u n).comp_tendsto ht).trans ?_).congr_left ?_
   · apply IsBigO.of_bound (‖a‖^n); exact .of_forall (fun y=> by change ‖(y*a)^n‖ ≤ _; rw [norm_pow,norm_pow,norm_mul,mul_pow]; linarith)
   intro y; simp [shell, smul_smul,mul_pow]
lemma blocks (s:Finset I)(u:I→X)(x':X)(K:I→ℕ)(hb:∀ i∈s,K i < s.card)(hr: ∀ i,i<s.card→∃ j∈s,K j=i): (fun t:ℝ=> block s (fun i=>t • u i) f (x+t • x'))=O[𝓝 0] fun t=>t^s.card:=by
  simp_rw [spelled s u f x K hb hr]
  exact .sum (A:=fun T t=> signed s T • (fwdDiff (t • spine s u K T))^[s.card] f (x+t • (x'+leanW s u K T))) fun T _=> (L.reveal ..).const_smul_left _
lemma annul (x':X)(h:n<s.card): block s u (L.bank n) x'=0:= by
  let K:I→ℕ:=fun i=> if h:i∈s then ((Fintype.equivFin s) ⟨i,h⟩).val else 0
  have hb j (h:j∈s):K j<s.card:=by unfold K; rw [dif_pos h]; simpa using (((Fintype.equivFin s) ⟨j,h⟩).isLt)
  have he j (h:j<s.card):∃ i∈s,K i=j:=by
     let k:Fin (Fintype.card s):=⟨j,by simpa using h⟩; let t:= (Fintype.equivFin s).symm k; exact ⟨t,t.property,by unfold K; rw [dif_pos t.property]; unfold t; simp [k]⟩
  have ht:=L.blocks s u x' K hb he
  refine pace (P:=fun i=>block s u (L.bank i) x') ?_ ht h
  intro k; let z(T: Finset I): X:= x'+∑ i∈T,u i
  let H(T : Finset I)(t:ℝ):Y:= f (x+t • z T)-shell (fun n=>L.bank n (z T)) k t
  refine (IsBigO.sum (A:=fun T t=>signed s T • H T t) (s:=s.powerset) (fun T _=> (L.jump (z T) k).const_smul_left _)).congr_left ?_
  intro t; dsimp only; rw [snow]; unfold H; simp only [smul_sub,sum_sub_distrib]; congr 1
  unfold shell block; simp_rw [smul_sum, smul_comm (signed ..)]; rw [sum_comm]
-- independent x': realize one more index to get equal
lemma clone (x' x'':X) (i:ℕ)(h:i=s.card): block s u (L.bank i) x'=block s u (L.bank i) x'':=by
   subst i
   let S:Finset (Option I):= s.image some; let v:Option I→X:=Option.elim' (x''-x') u
   have hf : Function.Injective (@some I):=fun i j h=>Option.some_injective _ h; have hp:S.card=s.card:=card_image_of_injective _ hf
   have hu:none∉S:=by simp [S]
   suffices hv: ∀ P:Finset I,∀ B:X→Y,∀ z,block (P.image some) v B z=block P u B z from (by
     have hh := L.annul (insert none S) v x' (n:=s.card) (by rw [card_insert_of_notMem hu,hp]; omega)
     rw [cons S _ _ _ hu,show x'+v none=x'' from (by change x'+(x''-x')=_; abel),hv s,hv s] at hh; exact (sub_eq_zero.mp hh).symm) -- mpr issue
   intro P B z; induction P using Finset.induction_on generalizing z with
   | empty=> rw [image_empty,start,start]
   | insert a s h ih=>
       rw [image_insert,cons _ v _ _ (by simp [h]),cons _ u _ _ h,ih,ih]; rfl
lemma draw (u:X): block s (fun _=>u) (L.bank s.card) 0=((Nat.factorial s.card:ℕ):ℝ) • L.bank s.card u:= by
  rw [rear, face]; simp_rw [zero_add,L.homo,smul_smul]; rw [←sum_smul]; congr 1
  have hp:= face (X:=ℝ) (Y:=ℝ) (f:=fun t=>t^s.card) (x:=0) 1 s.card
  rw [fwdDiff_iter_eq_factorial] at hp; simpa using hp.symm
end YM.FullVolume.Amp.Often

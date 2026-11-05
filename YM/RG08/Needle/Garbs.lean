import YM.RG08.Needle.Lace
/-!
# All-moment usage at a fixed step. Later quantify schedule charges.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {E H I α β:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{G:Gauge}{L c f p: Side}
variable {V U: Screed E α}{A:Canticle α}{K:Row α α}{k n r s t u v m D:ℕ} {a b σ w:ℝ}
variable {R W:Rooted E α r}
lemma sew_mint (h:Quire.Ink (mint k) R a) : Quire.Ink (mint k) (sew R) a := sewn_income _ (mint_pos _ _ _) (fun i s=> Equiv.prod_comp s (fun j=> Vale.dime k (i j).1)) h -- k
lemma jib_mint {R:Rooted E α (r+2)} (h: Quire.Ink (mint n) R a) (hx:K.strip σ b) (hp:0≤σ) (he:0≤b): Quire.Ink (mint n) (jib none K R) (‖batting r‖*(b*a)) := by
  apply sew_mint; apply Ink.scale; apply Ink.pour _ _ (mint_one _ _ _); apply budget_mono (budget_scale he h)
  · exact fun i=> mul_nonneg (mint_pos _ _ _ (stems i)) (norm_nonneg _)
  intro i
  have he' : mint n (stems i)≤ mint n i := by
    have hp (p:ℕ) (i:Beads α (p+1)): mint n (stem1 i) ≤ mint n i := by
      unfold mint; rw [Fin.prod_univ_succ (n:=p)]; exact le_mul_of_one_le_left (mint_pos _ _ _ (stem1 i)) (Carrier.liftCost_ge ..)
    exact (hp r (stem1 i)).trans (hp _ i)
  have hv: ‖tuneS K none i‖≤b := stroke_known K hx hp _ _ _ -- fix
  unfold Quire.knot; simp only [norm_smul,Function.comp_apply]; grw [he',hv]; exact le_of_eq (mul_left_comm ..)
  exact mint_pos ..
lemma mint_class {U:Rooted E α (r+1)} {V:Shale α (s+1)} (hv: Quire.Ink (mint (m*(r+s))) U a) (hb:0≤b) (hK:∀ i j,Charge (dime (m*(r+s))) (K i j) b)(hp: Quire.Ink (mint (m*(r+s))) V w):
    Quire.Ink (mint m) (clasp K U V) (‖syl r s‖*((b*((s+1:ℕ):ℝ)^(m*(r+s)))*(a*w))) := by
  let n:= m*(r+s); let f:ℝ:=((s+1:ℕ):ℝ)^n; have hf:0≤f:= by unfold f; positivity
  apply sew_mint; apply Ink.scale; apply Ink.pour _ _ (mint_one _ _ _); apply Ink.sires_cost (hv.prods (show Charge _ V w from hp)) _ _ (mul_nonneg hb hf)
  intro i
  let W:=(mint n i.1*mint n i.2)*f; have hh := mint_pos α _ n i.1; have hg:= mint_pos α _ n i.2
  have hW:0≤W:= mul_nonneg (mul_nonneg hh hg) hf
  rw [show b*f*(mint n i.1*mint n i.2)=W*b from (by unfold W; ring)]
  apply budget_mono (budget_scale hW (hK (i.1 0).2 (i.2 0).2)); exact fun _=>mul_nonneg (mint_pos ..) (norm_nonneg _)
  intro j
  have h : mint m (coral (i,j))≤W * dime n j := by
    let t:=girth (coral (i,j))
    let k:=(1+(girth i.1:ℝ))*(1+(girth i.2:ℝ)); have hk:0≤k:= by unfold k; positivity
    calc
     _ ≤ (1+(t:ℝ))^n := greater_bill ..
     _ ≤ (k*(s+1:ℕ)*(1+(size j:ℝ)))^n := by
       apply pow_le_pow_left₀ (by positivity); unfold k
       have he : (t:ℝ) ≤ (s+1:ℕ)*(girth i.1:ℝ)+girth i.2+(s:ℝ)*size j := by exact_mod_cast seized (i,j)
       let g:=(girth i.2:ℝ)
       have hm: (1+ (girth i.1:ℝ)) + girth i.2 ≤ (1+ (girth i.1:ℝ)) * (1+ (girth i.2:ℝ)) := by nlinarith [show 0 ≤ (girth i.1:ℝ) by positivity, show 0 ≤ (girth i.2:ℝ) by positivity]
       push_cast at *
       grw [← hm]
       -- after expansion
       nlinarith [show 0 ≤ (girth i.2:ℝ) by positivity,show 0≤(girth i.1:ℝ) by positivity,show 0≤ (size j:ℝ) by positivity,show 0≤ (s:ℝ) by positivity, show 0≤ (girth i.1:ℝ)*↑s*↑(size j)+(girth i.2:ℝ)*↑s*↑(size j) by positivity]
     _ ≤ _ := by unfold k W f; simp_rw [mul_pow]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul (lower_bill _ n) (lower_bill _ n) (by positivity) (mint_pos _ _ _ _)) (by positivity)) (Carrier.liftCost_pos ..)
  exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (mul_assoc ..)

variable [Fintype α][Fintype β]
lemma rung_price {Q : Row α β} (hq: Whole Q) (h : Polished R) : Polished (spring R Q) := by
  obtain ⟨σ,C,hσ,hE⟩:=hq
  let A:=max C 0; have hA:0≤A:=le_max_right ..; have he: Q.strip σ A:=strip_mono hE le_rfl (le_max_left ..)
  intro n
  obtain ⟨B,h⟩:= h n
  let M:=Carrier.widthCost σ n* A * Fintype.card β
  have hp: 0≤M:= mul_nonneg (mul_nonneg (zero_le_one.trans (Carrier.widthCost_ge hσ _)) hA) (Nat.cast_nonneg _)
  have ht(a):Charge (rug n) (fun i:Cover×β=> Q a i.2 i.1) M := by
    let f (i : β×Cover) := dime n i.2*‖Q a i.1 i.2‖
    have hh : SumBudget f M := budget_rows f (fun _=> Carrier.widthCost σ n*A) (fun i=> by unfold f; simpa only [mul_comm _ (Carrier.liftCost n _)] using Carrier.width_income hσ (he a i) n) (budget_finite (fun _=> mul_nonneg (zero_le_one.trans (Carrier.widthCost_ge hσ n)) hA) (by unfold M; rw [sum_const]; simp [mul_comm]))
    exact budget_pull (Equiv.prodComm ..) (Equiv.prodComm ..).injective hh
  have hv t : Charge (fun i=> mint n (fieldsAt (t,i))) (fun i=> flicker (fun _:Fin r=>Q) (t,i)) (M^r*mint n t) := by
    let P (k:Fin r) z:= rug n z*‖Q (t k).2 (z.2) (z.1)‖; have hh : SumBudget (fun i:Beads β r=>∏ j, P j (i j)) (M^r) := by simpa only [prod_const,card_univ,Fintype.card_fin] using budget_fin_prod _ fun i:Fin r=> ht (t i).2
    rw [mul_comm]; apply budget_mono (budget_scale (show 0 ≤ mint n t from mint_pos ..) hh); exact fun i=>mul_nonneg (mint_pos ..) (norm_nonneg _)
    intro i; unfold mint fieldsAt flicker P
    dsimp only; rw [norm_prod,prod_mul_distrib,← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun i _=> norm_nonneg _)
    rw [← prod_mul_distrib]; exact prod_le_prod (fun _ _=> Carrier.liftCost_pos ..) (fun _ _=> Carrier.liftCost_add ..)
  exact ⟨_, sew_mint (Ink.pour _ (Ink.sires_cost h _ _ (show 0≤M^r by positivity) hv) (mint_one _ _ _))⟩
private lemma grant_h {a:ℕ} (h: Polished R): Polished (grant a R) := by
  by_cases he:a=r; subst r; rwa [grant_self]
  unfold grant; rw [dif_neg he]; exact polished_zero _ _ _
lemma treble_shelf (h : Whole K)(hf : ∀ i j,Tunable (A i j))(hg:∀ i j, Glows (A i j))(hx : ∀ i j,Tidy (U i j))(hp:Lank U): Lank (murmur none K A U n) := by
  induction n using Nat.caseStrongRecOn with
  | zero => intro i j; rw [murmur]; exact hp i j
  | ind n ih=>
    intro k r
    rw [murmur_step]; refine polished_scale (polished_more ?_ ?_) _
    · obtain ⟨σ,C,hσ,H⟩:=h; intro i; obtain ⟨u,hp⟩:= ih n le_rfl k (r+2) i; exact ⟨_,jib_mint hp (strip_mono H le_rfl (le_max_left C 0)) hσ.le (le_max_right C 0)⟩
    apply polished_sum; intro p hp'; apply polished_sum; intro t ht; unfold Quire.hymn; apply polished_sum; intro j hj; apply grant_h
    have H:= ih p.1 (by have he:=mem_antidiagonal.mp hp'; omega) t.1 (j.1+1)
    have ht := show Glows (Refrain K A none p.2 t.2 (j.2+1)) from (Mending.both (X:=fun _ : ℕ=> A) (F:=A) (fun i j=>Mending.one _ (hg i j)) h board_end _ _ _).1 -- check
    intro m; obtain ⟨σ,C,hσ,hE⟩:=h; let D:=max C 0; have hd:0≤D:=le_max_right ..
    obtain ⟨S,W,hS,hW⟩:=ht
    obtain ⟨B,h⟩:= H (m*(j.1+j.2))
    let f:=Carrier.widthCost σ (m*(j.1+j.2))
    have he:∀ i k, Charge (dime (m*(j.1+j.2))) (K i k) (f*D) := fun i k=> by unfold Charge; simpa only [mul_comm _ (Carrier.liftCost _ _)] using Carrier.width_income hσ (strip_mono hE le_rfl (le_max_left C 0) i k) _
    exact ⟨_,mint_class h (mul_nonneg (zero_le_one.trans (Carrier.widthCost_ge hσ _)) hd) he (scarlet (U:=_) hW hS _|>.choose_spec)⟩
end YM.RG08.Needle

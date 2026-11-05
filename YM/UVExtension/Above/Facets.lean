import YM.UVExtension.Above.Doors
import YM.UVExtension.Guild.Bonnet
import YM.UVExtension.Lamppost.Promote
import YM.Planned.RECIPE_STARTUP_PORT.Layout

/-! # Startup bills. Fused with the *same* dictionary as is issued.
    Analytics are for normalized data (and don't assert nonmoving zeros
    on a nonphysical top branch).
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Above
open Function Filter Set RG Wilson Lattice MeasureTheory Precision Metric
open WilsonStartup Start Lamppost Timing Concert Guild
open Progress.DirectedRecipe Ovens Ovens.Pipes Planned.Port
open Real (log exp)
open scoped Matrix.Norms.Frobenius Topology Classical
variable {G : Gauge}

-- real price translations used also for lower levels
lemma floorE (p:BudgetPoint){n : Side}{v : ℝ}(R:Activities G n): (fork p G R.reg p.supportExponent).MeasureP (trill p G R.reg p.supportExponent R.E) v ↔ R.EBound p v:=by
  rw [fork_earns]; unfold coinE Activities.EBound BudgetPoint.mass -- coin check
  apply exists_congr; intro f; simp only [Push.AbsoluteSums.Footprint.Anchored,mul_comm]
lemma floorK (p:BudgetPoint){n : Side}{v : ℝ}(R:Activities G n): (bell R.forced p.B p.supportExponent).MeasureP R.K v ↔ R.KBound p v:= by
  have hk(f:ℕ→ℝ): (∀ i, SumBudget (fun j=>(bell R.forced p.B p.supportExponent).cost i j*f j) v) = (∀ x:Site n, SumBudget (fun i=> if x∈ (R.forced i).support then p.mass (R.forced i).support (f i) else 0) v):=by simp only [bell,ite_mul,zero_mul,BudgetPoint.mass]
  constructor <;> rintro h
  · obtain ⟨b,hb,hh⟩:= h.afloat; exact ⟨b,hb,hk b ▸ hh⟩
  obtain ⟨b,hb,hh⟩:=h; exact ⟨b,hb,(hk b).symm ▸ hh⟩

section slate
variable {G:Gauge} {n: Side} (p:BudgetPoint)(c:Clip)(F:ℕ ≃ (dictionary G n).Pellet)
lemma bets (i:ℕ)(v:ℝ): (payload c p G n v).regular i=v•(payload c p G n 1).regular i:=by
  simp only [payload]; split
  · unfold written; cases Padded.name (Sheet n) i <;> simp [Start.weight,mul_smul,mul_assoc]
  simp

lemma kicks (i:ℕ)(U:Config G n): ∃ f: ℂ→ℂ,Differentiable ℂ f∧ (∀ x : ℝ,f x= ((solid F p (payload c p G n x) i U:ℝ):ℂ))∧ ∀ x:ℂ,‖f x‖ = ‖solid F p (payload c p G n x.re) i U‖:=by
  unfold solid; split
  · have h(j:Ovens.Label):∃ f:ℂ→ℂ,Differentiable ℂ f∧ (∀ x:ℝ,f x= ((reach (payload c p G n x) j U:ℝ):ℂ)) ∧ ∀ x:ℂ,‖f x‖= ‖reach (payload c p G n x.re) j U‖ := by
       unfold Pipes.reach
       rcases j with i|i
       · dsimp only [payload,Sum.elim_inl]; split
         · unfold Start.paid; split
           · let φ:= (charge c p (Padded.name (Start.Foot n) i).val.2 U:ℝ)
             refine ⟨fun z=> Complex.exp (-z* φ), (by fun_prop), fun x=> by push_cast; rfl, fun x=> ?_⟩; rw [Complex.norm_exp,Real.norm_of_nonneg (Real.exp_pos _).le]; simp [φ]
           exact ⟨fun _=>0,differentiable_const _,by simp,by simp⟩
         exact ⟨fun _=>0,differentiable_const _,by simp,by simp⟩
       exact ⟨fun _=>0,differentiable_const _,by simp [payload],by simp [payload]⟩
    choose f hf he hF using h; exact ⟨fun z=>∏ j∈(F i).val,f j z, Differentiable.fun_finsetProd (fun j _=> hf j),fun x=> by simp_rw [he]; push_cast; rfl, fun z=> by simp_rw [norm_prod,hF]⟩
  exact ⟨fun _=>0,differentiable_const _,by simp,by simp⟩
end slate
open RG.Shoot
variable {a : Levels G} {P:Precision.Horizon a} {X:ChartRatio G}
    (k: Kin P X) (N n:ℕ)
abbrev temple (β:ℝ) := fromTop k N n β (Planned.Port.pot a N n) (Planned.Port.kettle a N n β)
variable {N} {ε b : ℝ} (h: Allows a N) (hv:Entry a N ε)
include h hv
lemma billT {β:ℝ}(hb:β∈band a N): Ingredients (pot a N n) (kettle a N n β) (a.budget N) (ε*a.clock.allowance N) (ε*a.clock.forcedAllowance N):=by
  obtain ⟨σ,κ,γ,hL,hP⟩:=hv.ripe
  refine ⟨κ,exp γ-1,exp γ-1, digests h.clip h.radius hL hb.1 ?_, hL.buys h.clip hb.1,hP⟩
  refine le_trans ?_ hv.cash; unfold Start.book overhead; have h₁:= item_pos G (a.budget N); have ht:‖β‖≤ 2*a.clock.hatBeta N:= by rw [Real.norm_of_nonneg (hL.slope.trans hb.1)]; exact hb.2
  gcongr

variable (hb:InsideB (a.clock.hatBeta N) b)
omit h
include hb
lemma fly {z:Mark}(hp:z∈lever.span) : let k:= inspire (a.clock.hatBeta N) b z none
    k.re∈band a N ∧ ‖k‖∈band a N := by
  intro t; let u:=a.clock.hatBeta N; let w:= ((stretchB u:ℝ):ℂ) * z none
  have hx: t=(b:ℂ)+w:= by unfold t inspire; rw [Function.update_self]
  have hu: u>0:= zero_lt_one.trans (a.fits.delayed _); have hZ:0≤ b:= by unfold InsideB at hb; linarith only [hu,hb.1]
  have hm: ‖w‖≤1/16*u := by
     unfold w; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ stretchB u from Real.rpow_nonneg hu.le _)]
     exact (mul_le_mul_of_nonneg_left (show ‖z none‖≤capK from (mem_ball_zero_iff.mp (Lamppost.within.mp hp none)).le) (Real.rpow_nonneg hu.le _)).trans hv.care
  have he : |w.re| ≤ 1/16*u:= (Complex.abs_re_le_norm _).trans hm
  have hL : t.re∈ band a N := by rw [hx,Complex.add_re, Complex.ofReal_re]; change _≤ _ ∧_≤ _; rw [abs_le] at he; constructor <;> linarith only [he.1,he.2,hb.1,hb.2,hu] -- hb exposed
  refine ⟨hL,hL.1.trans ((le_abs_self t.re).trans (Complex.abs_re_le_norm _)),?_⟩
  rw [hx]
  have hk := norm_add_le (b:ℂ) w; rw [Complex.norm_real,Real.norm_of_nonneg hZ] at hk
  linarith only [hk,hb.2,hm,hu]
include h
lemma bidT : let s:=(a.budget N); let B:= a.clock.hatBeta N; let f u:= temple k N n ((subgate B b (u:Arbor).val) none)
    Nonempty (ticketR lever s (drawer G (a.S.side N n)).reg s.supportExponent (fun i=>(f i).activities.E) (fun _=>ε*a.clock.allowance N)) ∧ Nonempty (Atlas (bell (addr (folio G (a.S.side N n)) s) s.B s.supportExponent) lever (fun i=>(f i).activities.K) (fun _=>ε*a.clock.forcedAllowance N)):=by
  intro s B f; let T:= pot a N n; let H:= (drawer G (a.S.side N n)); let c:= (a.params N).clip; let V x:=kettle a N n x
  let g i:=subgate B b (i:Arbor).val none; let w z:= inspire B b z none
  have hz z (hh:z∈lever.span) := fly hv hb hh; have hs(i:Arbor): w (lever.call i)= ↑(g i):= congr_fun (Lamppost.audits B b i.val) _
  have hg(i:Arbor): g i∈ band a N:=by have h:= (hz _ (lever.within i)).1; change (w _).re∈_ at h; rw [hs] at h; exact h
  have hW : Differentiable ℂ w:= (differentiable_pi.mp (inspireD B b)) _
  constructor
  · have he i x: (temple k N n x).activities.E i= x• (temple k N n 1).activities.E i:=by
       by_cases hp: i∈range (Rack.upE T)
       · obtain ⟨i,rfl⟩:= hp
         change (Rack.widen T _).regular _=_• (Rack.widen T _).regular _; simp only [Rack.widen, stuffed]; exact Above.bets _ _ _ _
       change (Rack.widen T _).regular i=_• (Rack.widen T _).regular i
       simp only [Rack.widen, blank _ _ hp,smul_zero]
    let J i j m:= trill s G H.reg s.supportExponent (temple k N n i).activities.E j m
    have hJ i j m : J i j m=i*J 1 j m:=by unfold J trill; rw [he]; exact left_mult ..
    refine ⟨⟨fun z j m=> w z* ((J 1 j m:ℝ):ℂ), fun i j m=> ?_,fun i j=> bumps _ _ (hW.mul_const _|>.differentiableOn),fun z hh=>?_⟩⟩
    · change w _* _=↑(J (g i) j m); rw [hs,hJ (g i),Complex.ofReal_mul] -- rw hJ occurrences!
    have hi:= billT n h hv (hz z hh).2; obtain ⟨F,hf,hF⟩:= ((floorE s (temple k N n ‖w z‖).activities).2 ((hi.gates (k.path N N) c ‖w z‖ 0).boundE)).afloat
    refine ⟨_,fun i=> ⟨(hf i).1,fun t=>?_⟩,hF⟩
    rw [norm_mul,Complex.norm_real]; have hp:= (hf i).2 t; change ‖J ‖w z‖ i t‖ ≤ _ at hp; rwa [hJ,norm_mul,norm_norm] at hp
  let F:= Start.enumeration G (a.S.side N n); choose Q hQ he hp using fun i U=>kicks s c F i U
  let M:= Concert.bell (addr F s) s.B s.supportExponent; let X i:= fused F s (V i)
  let X' x:= (temple k N n x).activities
  have hl x (hh:x ∈ band a N) : Readdress s (Rack.upE T) (Rack.nameUp F) (X x) (X' x):=(billT n h hv hh).address (k.path N N) c x 0 F
  -- want bound from billT for original F via transferring bound or directly complex on widened
  have hx z (hh:z∈lever.span): Meter.MeasureP M (fun i U=> Q i U (w z)) (ε*a.clock.forcedAllowance N):=by
    let x:=(w z).re
    let H:= billT n h hv (hz z hh).1
    obtain ⟨F',hf,hF⟩:= ((H.gates (k.path N N) c x 0).boundK)
    let e:= Rack.nameUp F; have ht:=hl x (hz z hh).1
    refine ⟨F'∘e, fun i=> ⟨(hf _).1,fun U=>?_⟩,fun i=>?_⟩
    · rw [hp]; change ‖(X x).K i U‖≤ _; rw [← ht.kernels i]; exact (hf _).2 U
    have h' := Push.AbsoluteSums.budget_pull e e.injective (hF i)
    let H:= (Concert.bell (addr (folio G (a.S.side N n)) s) s.B s.supportExponent)
    -- specialize costs explicitly
    suffices h: (fun j=> M.cost i j*(F'∘ e) j)=(fun j=> if i∈ ((X' x).forced j).support then s.mass ((X' x).forced j).support (F' j) else 0) ∘ e from h ▸ h'
    funext j; simp only [M,bell,Function.comp_apply,ite_mul,zero_mul]
    rw [show ((X' x).forced (e j)).support=_ from ht.sup j]; rfl
  have hX: Atlas M lever (fun d=> (X (g d)).K) (fun _=> ε*a.clock.forcedAllowance N) := ⟨fun z i j=> Q i j (w z),fun i j U=> by rw [hs]; exact he j U _, fun i j=> bumps _ _ ((hQ i j).comp hW|>.differentiableOn),hx⟩
  refine Lamppost.inserted _ _ _ (Rack.nameUp F) _ (fun i=>id) (fun d i k=> congr_fun (show (f d).activities.K (Rack.nameUp F i)=_ from (hl (g d) (hg d)).kernels i) _) (fun i hi d k=> congr_fun (show _=_ from (hl (g d) (hg d)).restK i hi) k) ?_ hX
  intro i j; dsimp only [M,bell]; rw [Rack.addr_sup]
end YM.UVExtension.Above

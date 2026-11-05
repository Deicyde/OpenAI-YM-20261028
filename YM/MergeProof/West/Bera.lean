import YM.MergeProof.West.Dew
import YM.Next.RANK.Purchased
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Vac.Numbers Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {ξ : Purse}
private lemma tall (u L b : ℝ) (hb : 0≤b) (hu : 1 ≤ u) (hL : 1<L) (h : 2 * Real.log u*(b+2) ≤ Real.log L) :
    ∀ᶠ s in atTop,u^ (Station.bump L b s) ≤ Perch.bill 1 s:= by
  have he : 0 ≤ Real.log u:=Real.log_nonneg hu; have hx : 0< Real.log L:=Real.log_pos hL
  filter_upwards [boil_rate.eventually_ge_atTop (2*Real.log u)] with s hs
  let X:=bump L b s; let f : ℝ:= boil s; have hf : 0≤f:=boil_pos _
  have hm : (X:ℝ)< (b+2)*f/Real.log L+1:= by
    have hp : Real.log ((P s)^b*(P s)^2)=(b+2)*f:= by unfold P; rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (Real.exp_pos _),Real.log_pow,Real.log_exp];push_cast;unfold f boil y; ring
    unfold X bump want; rw [hp]; exact Nat.ceil_lt_add_one (by positivity)
  have hp : (X:ℝ)*Real.log u ≤ f:= by
    have hh := mul_le_mul_of_nonneg_right hm.le he; rw [add_mul,div_mul_eq_mul_div,one_mul] at hh
    have hv : (b+2)*f* Real.log u / Real.log L ≤ f/2:= by apply (div_le_iff₀ hx).2;linarith only [mul_le_mul_of_nonneg_left h hf]
    change 2*Real.log u ≤ f at hs; linarith only [hh,hv,hs]
  rw [← show Real.exp (Real.log u)=u from Real.exp_log (by linarith), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr; rw [mul_one]; exact hp
private lemma gjoy (P:Purse)(n:ℕ): ∀ᶠ s in atTop,∀ u∈Set.Icc (s/2) s,
     let H:=P.era; let a:=H.coast; let l:=Paint.trib a.a u; let y:= Perch.bill (-1) s
     Real.exp l*(Perch.gas a u)^2+(n:ℝ)*Perch.bill (-2) s * rentQ a.Q (load H+1) ≤ y:=by
   let H:=P.era; let a:=H.coast;let g:=a.a
   have hg:=a.posA;let e:=load P.era+1;let c:=rentQ a.Q e;let f:ℝ:=n*c+1
   have he (u) : Perch.gas a u= Real.exp (-trib g u):=by rw [gas,trib];unfold g;simp
   have hx u: Real.exp (trib g u)*(gas a u)^2=gas a u:=by rw [he,pow_two,← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
   filter_upwards [Perch.force hg 2 0 (by norm_num) (by norm_num), Paint.absorb (-2) (-1) (by norm_num) f] with s h H u hu
   have ht: gas a u ≤ bill (-2) s:=by rw [he];unfold Perch.bill trib; apply Real.exp_le_exp.mpr; linarith only [h u hu]
   intro H' a' l y
   apply le_trans _ H; rw [hx]; change gas a u+(n:ℝ)* _ *c≤ _; unfold f; linarith only [ht]

-- Shelf currency.Even though use any wind, compare explicitly floor
private lemma curl_price {u n:ℕ} {Y:ℝ} (h:Volt Y (qquiet ξ.credit n))(ht:Y+ξ.f+1< -4)(hm:2 ≤ u): ∀ᶠ s in atTop,(↑(2^n:ℕ):ℝ)*proDue ξ s u n ≤ bill (-4) s:= by
   have he:Volt (Y+1) (fun s=> sheen ξ s n):= h.times (btvolt (degrFt ξ n))
   have hh:Volt ξ.f (fun s=> loot ξ s u):=(Volt.pulse (cashFt ξ u)).high (cash_le _ _ hm)
   apply ((((hh.times he).scale _).scale (↑(2^n:ℕ):ℝ))).met; linarith only [ht]
-- brakes thresholds.Leave witnesses
structure Portion (z f:ℝ)(u:ℕ):Prop where
    lift (n:ℕ)(h:n ≤ u):∃ Y,Volt Y (qquiet z n)∧ Y+f+1< -4
structure Plinks (z v:ℝ)(g D u:ℕ):Prop where
    pays (n:ℕ)(h:n ≤ u): (∃ Y,Volt Y (gbt z D n)∧ Y+(-v)<0)∧(∃ Y,Volt Y (brr z D n)∧ Y+(-v)< -(g:ℝ))∧ (∃ Y,Volt Y (brr' z D n)∧ Y+(-v)< -3/2)

lemma pays_p (z:ℝ)(u:ℕ):∀ᶠ f in atBot, Portion z f u:=by
   have hp:= (show ∀ᶠ f in atBot,∀ n ∈ range (u+1),∃ Y,Volt Y (qquiet z n)∧ Y+f+1< -4 from
      (eventually_all_finset _).2 fun n _=> by obtain ⟨y,hy⟩:= quists z n; exact (eventually_lt_atBot (-4-y-1)).mono fun f h=>⟨_,hy,by linarith only [h]⟩)
   exact hp.mono fun z h=>⟨fun n hx=>h n (mem_range.mpr (by omega))⟩
lemma earns_p (z:ℝ)(g D u:ℕ):∀ᶠ f in atTop,Plinks z f g D u:=by
   have hp n: ∀ᶠ f in atTop, (∃ Y,Volt Y (gbt z D n)∧ Y+(-f)<0)∧(∃ Y,Volt Y (brr z D n)∧ Y+(-f)< -(g:ℝ))∧ (∃ Y,Volt Y (brr' z D n)∧ Y+(-f)< -3/2):=by
      obtain ⟨X,hX⟩:= glosier z D n; obtain ⟨Y,hY⟩:= briers z D n; obtain ⟨Z,hZ⟩:= brierez z D n
      filter_upwards [eventually_gt_atTop X,eventually_gt_atTop (Y+g),eventually_gt_atTop (Z+3/2)] with f h he hv
      exact ⟨⟨_,hX,by linarith only [h]⟩,⟨_,hY,by linarith only [he]⟩,⟨_,hZ,by linarith only [hv]⟩⟩
   filter_upwards [(eventually_all_finset (range (u+1))).2 (fun n _=>hp n)] with f ht; exact ⟨fun n h=> ht n (mem_range.mpr (by omega))⟩

structure Coul (ξ:Purse)(u:ℕ):Prop where
   tall(n:ℕ)(h:n ≤ u):6*n+3 ≤ ξ.horizon/(3+2*n)
   flare : 1-(ξ.goal:ℝ) ≤ -((u:ℝ)*ξ.era.coast.V)-2
   pre : Portion ξ.credit ξ.f u
   far : Plinks ξ.credit ξ.foil ξ.goal ξ.taylor u
structure HLane (p:Purse)(u:ℕ)(L:Side):Prop where
   run (n:ℕ)(h:n≤ u): 2*Real.log (crest p.L (n*p.taylor))*(p.band+2) ≤ Real.log (L.val:ℝ)
lemma lsizing (p:Purse)(u:ℕ):∃ k:ℕ,∀ (L:Side), k≤ L.val→HLane p u L:=by
   obtain ⟨k,hk⟩:= eventually_atTop.mp ((eventually_all_finset (range (u+1))).2 fun n _=> ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (2*Real.log (crest p.L (n*p.taylor))*(p.band+2))))
   exact ⟨k,fun L h=>⟨fun n hn=> hk _ h n (mem_range.mpr (by omega))⟩⟩
variable {u n : ℕ}
lemma joys (H:Coul ξ u) (L':Side)(hl:HLane ξ u L') (ht:1 < (L'.val:ℝ))(hb:0 ≤ ξ.band)(hp:ξ.budget)(hu:2 ≤ u)(hn:n ≤ u) : ∀ᶠ s in atTop,Caff (G:=G) ξ s (bump L'.val ξ.band s) u n:=by
   obtain ⟨a,ha,h⟩:= H.pre.lift n hn
   obtain ⟨⟨X,hX,hK⟩,⟨y,hy,hc⟩,⟨V,hV,hT⟩⟩:= H.far.pays n hn
   let f:=ξ.foil; let v:= ξ.sends
   let Q:=rentQ ξ.era.coast.Q (load ξ.era);let b:ℝ:=↑(2^n:ℕ)
   have h': ∀ᶠ s in atTop,b*(Q*(brr ξ.credit ξ.taylor n s * v s))≤ ξ.demand s:= (((hy.times (Volt.pulse _)).scale _).scale b).met hc
   filter_upwards [tall (crest ξ.L (n*ξ.taylor)) L'.val ξ.band hb (pay_crest ξ.loan _) ht (hl.run n hn), curl_price ha h hu,(candleM _ hX (-f)).met hK,h', (candleM _ hV (-f)).met hT, gjoy ξ n, awakens n ξ hp (G:=G)] with s hA hL hP hW hG hWQ hv
   obtain ⟨h1,h2,h3⟩:= pity ξ s n; exact ⟨H.tall _ hn,hA,H.flare,hL,h1.trans_le (le_trans hP (by simp [Perch.bill])),h2.symm ▸ hW,hWQ,hv,h3.trans_le hG⟩
end YM.Next.Rank.Tapes.West

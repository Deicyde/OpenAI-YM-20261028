import YM.UVExtension.Wren.Branching
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration Next.Scheduling
open Song Strata Gala Concert Geo Chains
namespace Crumble
-- Low Fresh. shapeBound from Width. all left tests via scaleˆ.
variable {Q:ι→ PathData G}{W:PathData G}{A:Listing G c}{K:ι→ Collection.Source G c}
    (p:BudgetPoint)(h:Revenues v u Q W){Z: Clip}(hz:Decent Z p)(hp: Geo.Width p Z u)
include h
variable [NeBot v]
lemma shelvesV (A:Listing G c)(n): shelves A W p=shelves A (Q n) p:=by
   have hx : highEntry G (Q n) (n:=c)=highEntry G W:=by
       funext i; rcases i with ⟨i,j|j⟩; exact ((songsL h).landsH n (i,j)).symm; exact ((songsH h).landsH n (i,j)).symm
   have he : incoming A W p=incoming A (Q n) p:= by unfold incoming; rw [hx, Ski.foots h]
   have ht : Collection.soft A W p=Collection.soft A (Q n) p:=by unfold Collection.soft; rw [Ski.foots h]
   have hU : ∀ (X Y:Ovens.Pipes G c), X.reg=Y.reg → X.kernel=Y.kernel→X.softer=Y.softer→X=Y:=by rintro ⟨a,b,c,d⟩ ⟨g,v,x,z⟩ he hv hx; dsimp only at he hv hx; subst_vars; rfl
   exact hU _ _ (funext fun i=> congr_fun he _) rfl (funext fun i=> congr_fun ht _)

include hz
-- use `Tune` scale mark bounds direct u≥1/Relaxation.
lemma records : Notes v p (lowEntry G W p (n:=c)) (fun n (i:Faces c)=> i.2.fresh (Q n) Z 0 1 ∘ i.1.view):=by
    let a n(j:Low):= |j.mark (Q n) Z| *lowCost G p (j.length (Q n)); have he:Swift v a:=Ski.acclaim h p
    let C:=Push.Local.turnCost p.order p.power*p.threshold^2; have hC:0 ≤ C:=mul_nonneg (turnFee_pos p).le (sq_nonneg _)
    let A n(i:Faces c):= i.2.fresh (Q n) Z 0 1 ∘ i.1.view
    have hQ n(i:Faces c): p.Regular (lowEntry G W p i).support (A n i) ∧ p.supBounds (lowEntry G W p i).site (lowEntry G W p i).support (A n i) (C*a n i.2):=by
        rw [← Ski.foots h p n]; let k:=i.1; let g:Config G c→ℝ:= i.2.fresh (Q n) Z 0 1; have he:=i.2.fresh_regular (Q n) Z (0:Site c) hz 1; refine ⟨k.regular he,?_⟩
        have hv:= Seat.sup k he (Bill.sup (i.2.fresh_bill (Q n) Z 0 hz 1) (fun _ h=>h)); rw [abs_one,one_mul] at hv; unfold C; rw [mul_assoc]; exact hv
    have hh : Swift v (fun (i:ι)(_ : Seat c)=> C):=Swift.sight fun _=> ⟨_,Eventually.of_forall fun _=>⟨hC,le_rfl⟩⟩
    let b i (j:Faces c):=C*a i j.2
    have hb:Swift v b:= hh.mixes he
    obtain ⟨r,hr⟩:=hb.books
    refine ⟨fun i j=> (hQ i j).1, ⟨_,hb,Eventually.of_forall (fun i j=>tap_bound.mp (hQ i j).2|>.2)⟩,fun i=>?_⟩ -- q .2
    -- fix zero-mark issue condition globally and take one nonzero proof, not assume
    let f (n):= i.2.mark (Q n) Z; let T:Config G c→ℝ:=( i.2.proxy W 0-i.2.plain W 0) ∘ i.1.view
    have ht n : A n i=f n • T:=by
       funext j; unfold A Low.fresh T; dsimp only [Function.comp_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]; rw [one_mul,Ski.pins h,Ski.pays h]
    let A':= Choir.onstage p (lowEntry G W p) i G
    have hv (n) (x:A'): x.read (A n i)= f n*x.read T:=by rw [ht]; exact WilsonStartup.Start.left_mult _ _ _
    change Tune v (fun n (a:A')=> a.read (A n i)); simp_rw [hv]
    by_cases he: ∀ n,f n=0
    · simp_rw [he,zero_mul]; exact Tune.nil
    push Not at he; obtain ⟨n,hn⟩:=he
    apply (Tune.constant _ _ (Ski.marks h i.2)).mul
    have hz:0 < |f n|:=abs_pos.mpr hn
    refine ⟨⟨(|f n|)⁻¹*b n i,Eventually.of_forall fun i' k=> ?_⟩,fun ε he=> Eventually.of_forall fun n i=> by rw [sub_self,norm_zero]; exact he.le⟩
    rw [← mul_le_mul_iff_right₀ hz,← mul_assoc,mul_inv_cancel₀ hz.ne',one_mul]; have hp:= (tap_bound.mp (hQ n i).2).2 k; rw [hv n k,norm_mul] at hp; exact hp

lemma houses (A:ι→ℝ){t:ℝ} (hf:Tendsto A v (𝓝 t)): Notes v p (lowEntry G W p (n:=c)) (fun n (i:Faces c)=> i.2.fresh (Q n) Z 0 (A n) ∘ i.1.view):=by
    convert (records p h hz).swells A hf using 1; ext; dsimp [Low.fresh]; ring

omit hz
-- live terms continuity bounded independent of readings. Compact Gauge fields. `Decent` could weakened to relaxation.
omit h in
lemma flatSongs(f: Config G c→ℝ)(B:ℝ)(hp:∀ V, ‖f V‖≤B): Tune v (fun _=>f):= ⟨⟨_,Eventually.of_forall fun i=>hp⟩,fun ε he=> Eventually.of_forall fun _ h=> by rw [sub_self,norm_zero]; exact he.le⟩
lemma lemS (Z:Clip)(U:Config G c)(x:PlaqAxes)(t:ℕ ×ℕ)(n:ι) (b:Site c) : Low.live (Q n) Z (x,Sum.inr t) p b U = (if PathData.kept Z p.threshold b U then Low.mark (Q n) Z (x,.inr t)*Low.plain W (x,.inr t) b U else 0):=by
   unfold Low.live; dsimp only; simp_rw [Ski.pays h]; simp only [Sum.elim_inr]
lemma perpetual (x:Low) (b:Site c)(Z:Clip) : Tune v (fun n V=> x.live (Q n) Z p b V):=by
   rcases x with ⟨y,z|z⟩
   · let d:Low:= ⟨y,.inl z⟩; have hp : (fun n (V:Config G c)=>d.live (Q n) Z p b V)=(fun _ : ι=>d.live W Z p b):=by funext n V; unfold Low.live; dsimp only [d,Sum.elim_inl]
     rw [hp]; exact flatSongs (v:=v) (d.live W Z p b) _ (fun V=> d.shapeBound W Z b V)
   let x:Low:=⟨y,.inr z⟩; let V:= x.plain W b
   obtain ⟨C,hC⟩:= ((isCompact_range (x.plain_cont W b)).isBounded).exists_norm_le
   have he := ((Tune.constant (X:=Config G c) _ _ (Ski.marks h (C:=Z) x)).mul (flatSongs (v:=v) V _ fun i=> hC (V i) (mem_range_self _))).mask (fun i:Config G c=> PathData.kept Z p.threshold b i)
   exact he.switch (Eventually.of_forall fun i=> funext fun v=> (lemS p h Z v y z i b).symm)
lemma proxies (x:Low) (o:Site c): Tune v (fun n V=> x.proxy (Q n) o V):=by
   obtain ⟨C,hC⟩:=((isCompact_range (x.proxy_cont W o)).isBounded).exists_norm_le; simp_rw [Ski.pins h]; refine ⟨⟨C,Eventually.of_forall fun i V=> hC _ (mem_range_self _)⟩,fun ε h=> by filter_upwards with i V; rw [sub_self,norm_zero]; exact h.le⟩
variable {α β:ι→ ℝ} {e t':ℝ} (he:Tendsto α v (𝓝 e))(hr:Tendsto β v (𝓝 t'))
include he hr
lemma miracles (k:Low)(o:Site c) (Z:Clip) : Tune v (fun n V=> k.loan (Q n) Z o p (α n) (β n) V):=by
    let X(n:ι)(V:Config G c):= α n+β n; have ht:= (Tune.constant _ _ (he.add hr)).mul (perpetual p h k o Z)
    have hb:= ((Tune.constant _ _ (hr.mul (Ski.marks h (C:=Z) k))).mul (proxies (v:=v) h k o)).mask (fun V:Config G c=> Healthy p.threshold {o} V) -- p unused
    have hd: Tune v (fun n V=> (α n+β n)*k.live (Q n) Z p o V - if Healthy p.threshold {o} V then β n*k.mark (Q n) Z *k.proxy (Q n) o V else 0):= ht.sub hb
    apply (hd.mask (fun V:Config G c=> ¬Healthy p.threshold (k.home W p o) V)).switch; filter_upwards with n; funext v'; unfold Low.loan; rw [Ski.lands h]; split_ifs <;> rfl
include hp
lemma carries : Transit v (fun n (i:Faces c) U=> Low.loan (Q n) Z i.2 0 p (α n) (β n) (i.1.view U)):=by
    have ht: 1≤ Z.relaxation*u:= by linarith [hp.2.1] -- hp. relaxation
    let t a b:= Collection.hitPower p G a b; let A:= t e t'+1; have hA: 0 ≤ A:= add_nonneg (hitPower_pos ..) zero_le_one
    have hy : ∀ᶠ n in v, t (α n) (β n) ≤ A:=(show Tendsto _ _ (𝓝 (t e t')) from (Continuous.tendsto (show Continuous (fun r:ℝ ×ℝ=>t r.1 r.2) from (by unfold t hitPower; fun_prop)) _).comp (he.prodMk_nhds hr)).eventually_le_const (by unfold A; simp)
    let f n (i: Low):=|i.mark (Q n) Z| *Real.exp (u*i.length (Q n)); have hv:Swift v f:= Ski.thunder h
    have hw: Swift v (fun (_:ι) (_:Seat c)=> A):=Swift.sight fun i=> ⟨_,Eventually.of_forall fun n=>⟨hA,le_rfl⟩⟩
    refine ⟨⟨_,hw.mixes hv,?_⟩,fun i=>(miracles p h he hr i.2 (0:Site c) Z).cues (Seat.view i.1)⟩
    filter_upwards [hy] with n hn i U
    apply (Low.loan_bound ..).trans; unfold shapeLoss f; let l:ℝ:= (i.2.length (Q n):ℝ); have he: 0 ≤ l:= Nat.cast_nonneg _; let e:=α n; let b:= β n
    change t e b* Real.exp (l / Z.relaxation)*_ ≤ _; rw [mul_assoc,mul_comm (|i.2.mark (Q n) Z|)]; exact mul_le_mul hn (mul_le_mul_of_nonneg_right (Real.exp_monotone ((div_le_iff₀ Z.radius_pos).mpr (by nlinarith))) (abs_nonneg _)) (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) hA
end Crumble
end YM.UVExtension.Wren

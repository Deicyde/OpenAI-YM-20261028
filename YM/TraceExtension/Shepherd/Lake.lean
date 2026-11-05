import YM.TraceExtension.Shepherd.Grovel
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory Cells
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]{n:Side}(R:Rep G n)(x:Site n)(d:Axis)(ν:G.El→ G.El) (J:Config G n→ G.El →ℂ) {P:Support n}
    {σ A v δ u:ℝ}(h:R.Lawful σ A v δ u)(H:Geo.Width R.p R.clip σ)(hv:WilsonStartup.Decent R.clip R.p)(he:4 ≤ R.p.supportExponent) (m:ℕ) {D:ℝ} (hJ: ProofC R x J ν P D)
local notation "a"=>posDir d
local notation "r!"=> rink R x (posDir d) m J ν
def peck (b:Bool) (c:ℂ):ℂ:= if b then star c else c
lemma pecked (b:Bool) (c:ℂ): ‖peck b c‖=‖c‖:=by unfold peck; split<;>simp
abbrev Ink (s:Seat n) (b:Bool)(U:Config G n)(v:G.El):= peck b (J (s.view U) v)
abbrev joinD (s:Seat n):= affine s.1 s.2 x
abbrev rose (s:Seat n):= (posDir d).rotate s.1
include hJ
lemma peering (s:Seat n)(b:Bool): ProofC R (joinD x s) (Ink J s b) ν (s.spread P) D:=by
    have hp: Continuous s.view:= (continuous_pull (G:=G) ..); have hx: Measurable (fun p: Config G n × G.El=> (s.view p.1,p.2)):= (hp.measurable.comp measurable_fst).prodMk measurable_snd
    refine ⟨?_,fun j U V hu=> ?_,fun g U j=>?_,fun U j H=>?_,hJ.turns,hJ.price,hJ.less,hJ.borel⟩
    · obtain ⟨c,hc⟩:=hJ.env.cost; refine ⟨(show Measurable (fun p: Config G n × G.El=>peck b (J (s.view p.1) p.2)) from ?_),c,fun p=> (pecked ..).le.trans (hc (s.view p.1,p.2))⟩
      have hv : Measurable (fun p: Config G n × G.El=> J (s.view p.1) p.2):= hJ.env.meas.comp hx
      unfold peck; split; exact continuous_star.measurable.comp hv; exact hv
    · exact congr_arg (peck b) (hJ.eye j _ _ (Push.Local.agrees_pull _ _ hu))
    · unfold Ink Seat.view; rw [Push.Local.pull_gauge]; exact congr_arg (peck b) (hJ.gear (g ∘ affine s.1 s.2) (s.view U) j)
    have hz: x∈P→True:=by simp
    have hv' := (s.healthy (R.p.threshold/4) {x} U).2 (hJ.charm (s.view U) j (fun ht=> H (by simp [Ink,peck,ht])))
    simpa only [Seat.spread,image_singleton] using! hv'
omit hJ
include h
lemma printS (s:Seat n)(b:Bool)(U:Config G n)(j:G.El): rink R (joinD x s) (rose d s) m (Ink J s b) ν U j = peck b (rink R x (posDir d) m J ν (s.view U) j):=by
   have hx:∀ U:Config G n, field R m (s.view U)=field R m U:= fun V=> congr_fun (crew_pull R h m s) V
   unfold rink spur Ink aura stunt; rw [← pull_shift,hx,hx]
   unfold peck; split <;> simp only[star_mul,Complex.star_def,Complex.conj_ofReal] <;> first| rfl| ring
omit h
lemma eval_leaf (i:V)(F:G.El→ℂ)(h: Measurable F): (∫ v:Rain V G,F (v i) ∂freq V G)=∫ v,F v∂G.probHaar:=by
    let f(v:Rain V G):=v i; have hx : MeasurePreserving f (freq V G) G.probHaar:= measurePreserving_eval _ _
    calc
      _ = ∫ v,F v∂Measure.map f (freq V G):= (integral_map hx.measurable.aemeasurable h.aestronglyMeasurable).symm
      _ = _ := by rw[hx.map_eq]
include hJ h H hv he
lemma passport (s:V→Seat n)(b:V→Bool)(o : V ↪ Site n) (ho:∀ i,o i=(s i).2)(hx:x∈P)(hq : 0∈P)(k:ℕ)(hk: coverNumber R.p.B P≤k)
    (hs:∀ i j,i≠j→ 2*pierSize R.p m k+2 < separation (joinD x (s i)) (joinD x (s j))) :
    Palace R (joinD x ∘ s) (rose d ∘ s) ν o (fun i=>(s i).spread P) (fun i=> Ink J (s i) (b i)) m D:= by
    let z:=joinD x ∘ s; have hg(i): z i∈Seat.spread (s i) P:= mem_image_of_mem _ hx
    have hm(i): o i∈ Seat.spread (s i) P:= by rw [ho]; exact (s i|>.reg P hq).anchor
    refine ⟨fun i=>peering R x ν J hJ (s i) _, hJ.turns,hJ.borel,hg,hm,fun i j he=> ?_, fun i _ j _ hij=>?_⟩
    · by_contra hh; have hp (x:Site n)(a':Step): separation x (a'.used x).1 ≤ 1:=by
         unfold Step.used; split
         next h=> change separation x (x-step a'.dir)≤1; unfold separation; rw[sub_sub_self]; exact pdist_step _
         next=> simp
      have hl1:= hp (z i) (rose d (s i)); have hl2:= hp (z j) (rose d (s j)); let t:= ((rose d (s i)).used (z i)).1; have ht: separation t (z j) ≤ 1:=by rw [show t=((rose d (s j)).used (z j)).1 from congr_arg Prod.fst he,separation_comm]; exact hl2
      have hz:= Nat.lt_of_lt_of_le (hs i j hh) ((separation_triangle (z i) t (z j)).trans (Nat.add_le_add hl1 ht)); omega
    refine disjoint_left.mpr fun p hi hj=>?_ ; let V'(v:V):= Seat.spread (s v) P; let a':= pierSize R.p m k
    have he(v:V)(hv:p∈inspected (bluff R z V' m v)): separation p (z v) ≤ a':= by rw[bluffP] at hv; exact meetP R m ((Seat.visit_count ..).trans_le hk) (hg v) (hg v) hv
    have hy:=hs _ _ hij; change 2*a'+ _ < separation (z i) (z j) at hy; have H':= hy.trans_le (separation_triangle (z i) p (z j)); rw [separation_comm (z i)] at H'; have hn:=he i hi; have hq:=he j hj; omega
lemma copyP (s:V→Seat n) (b:V→Bool) (o:V↪Site n) (hx: Palace R (joinD x ∘ s) (rose d ∘ s) ν o (fun i=> (s i).spread P) (fun i=> Ink J (s i) (b i)) m D) (v:V) :
   let Q:= hull R m hx.terse hx.seats (d:=rose d ∘ s) (J:=fun i=> Ink J (s i) (b i)) (ν:=ν)
   plebe (markA Q) (highA Q) v=fun U=> peck (b v) (lensF R x d ν J m ((s v).view U)):=by
   intro Q; let s':=s v; let b':=b v; let x':= joinD x s'; let J' := Ink J s' b'; let q:= rink R x' (rose d s') m J' ν; have hp:Envelope (uncurry q):= extraCred R h H hv he m hx _|>.1
   funext U; have he': Measurable (fun i=> q U i-J' U i):= (hp.meas.comp (show Measurable (Prod.mk U (β:=G.El)) from measurable_const.prodMk measurable_id)).sub ((peering R x ν J hJ s' b' |>.env.meas).comp (show Measurable (Prod.mk U (β:=G.El)) from measurable_const.prodMk measurable_id))
   unfold plebe; change (∫ k:Rain V G,q U (k v) - J' U (k v) ∂freq V G) = _
   rw [eval_leaf v _ he']; unfold q; unfold x' J' ; simp_rw[printS R x d ν J h m]; unfold b' s' Ink lensF peck;split
   next h=>simp_rw [←star_sub,Complex.star_def,integral_conj]
   next=>rfl
end YM.Trace.Shepherd

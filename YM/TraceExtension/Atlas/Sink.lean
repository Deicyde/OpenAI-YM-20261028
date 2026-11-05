import YM.TraceExtension.Atlas.Zone
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction RG Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S){H:(Bel C.book).Hierarchy}{𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C}
abbrev trail:=𝓝[>] (0:ℝ)
def LogV(x:ℝ):= Real.log x⁻¹
private lemma age(L:Schedule){x:ℝ}(h:0<x):∃ i:ℕ,L.a i < x:= (L.shrinks.eventually (gt_mem_nhds h)).exists

def glen(L:Schedule)(x:ℝ):=if h:0<x then Nat.find (age L h) else 0
lemma glen_first(L:Schedule){x:ℝ}(h:0<x):L.a (glen L x) < x:=by rw [glen,dif_pos h];exact Nat.find_spec (age L h)
lemma glen_off(L:Schedule){x:ℝ}(h:0<x)(hv:0 < glen L x):x ≤ L.a (glen L x-1):=by
    set i:=glen L x; refine not_lt.mp fun hx=> ?_
    rw [show i=glen L x from rfl,glen,dif_pos h] at *; exact Nat.find_min (age L h) (by omega) hx
lemma glen_leads(L:Schedule):Tendsto (glen L) trail atTop:=by
    apply tendsto_atTop.2; intro k; filter_upwards [self_mem_nhdsWithin,(show ∀ᶠ s in trail,s<L.a k from (Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (L.a_pos k))))] with x h hx; by_contra! he; apply ((glen_first L (show 0<x from h)).trans hx).not_ge (L.strictAnti.antitone he.le)
lemma pace_log{A:Levels G}(h:G.Simple)(H:PostT A): Tendsto (fun x=> LogV x/A.clock.hatBeta (glen A.S x)) trail (𝓝 G.slopeConstant⁻¹):=by
    let m:=glen A.S; let p(i):= A.clock.hatBeta i; let c:=G.slopeConstant;let k(i):= A.S.scale i; let b:=A.clock.bar
    have he:Tendsto (fun i=>k i/p i) atTop (𝓝 c⁻¹):=by
       have hg(i):p i=b+c*k i:=rfl; have ht:= tendsto_const_nhds (x:=b) |>.div_atTop (hrate A h); have hp:= ((tendsto_const_nhds (x:=(1:ℝ))).sub ht).div_const c; rw[sub_zero,one_div] at hp; refine hp.congr (fun i=>?_); change (1-b/p i)/c=_; have hc:p i≠0:=(bell ..).ne'; have hn:c≠0:= (Gauge.slopeConstant_pos h).ne'; field_simp;rw[hg];ring
    have hz:Tendsto (fun i=>Real.log (p i)/p i) atTop (𝓝 0):=(Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (hrate A h));
    have hx:Tendsto (fun i=> k (i-1)/p i) atTop (𝓝 c⁻¹):=by
       apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (show Tendsto (fun i=> k i/p i-Real.log (p i)/p i) atTop (𝓝 c⁻¹) from by simpa only [sub_zero] using! he.sub hz) he
       · filter_upwards [eventually_gt_atTop 0] with i hi; rw[← sub_div]; apply div_le_div_of_nonneg_right _ (bell ..|>.le)
         have hp:= H.bloom (i-1); let t:ℝ:=(A.S.block (i-1)).val; have he : k i=k (i-1)+Real.log t:=by
            cases i with
            | zero=>omega
            | succ i=> simp only [Nat.add_one_sub_one]; exact A.S.scale_succ i
         rw[he]; have hc:0<t:=by unfold t; positivity
         have hh: p (i-1)≤ p i:= monoBeta A h (Nat.sub_le i 1)
         have hz:t ≤ Real.log (p i):=hp.trans (Real.log_le_log (bell ..) hh)
         linarith only [Real.log_le_sub_one_of_pos hc,hz]
       apply Eventually.of_forall; intro i; exact div_le_div_of_nonneg_right (show k (i-1)≤ k i from Real.log_le_log (inv_pos.mpr (A.S.a_pos _)) (inv_anti₀ (A.S.a_pos _) (A.S.strictAnti.antitone (Nat.sub_le i 1)))) (bell ..|>.le)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hx.comp (glen_leads A.S)) (he.comp (glen_leads A.S)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,(glen_leads A.S).eventually_gt_atTop 0] with i hi hu
      have hP:0 < i:= hi; exact div_le_div_of_nonneg_right (Real.log_le_log (inv_pos.mpr (A.S.a_pos _)) (inv_anti₀ hP (glen_off _ hP hu))) ((bell A _).le)
    filter_upwards[self_mem_nhdsWithin] with i hi; have hP:0 < i:=hi; exact div_le_div_of_nonneg_right (Real.log_le_log (inv_pos.mpr hP) (inv_anti₀ (A.S.a_pos _) (glen_first _ hP).le)) ((bell ..).le)

-- Coupling comparison: explicit positive branch at nearest Wilson spacing, broad leading precision.
def wilson (Z:Arch C)(x:ℝ):= (Real.sqrt (Z.β (glen C.S x)))⁻¹
structure Coupling (G:Gauge) (u:ℝ→ℝ):Prop where
    positive:∀ᶠ i in trail,0 < u i
    running:Tendsto (fun i=> LogV i*u i^ (2:ℕ)) trail (𝓝 G.slopeConstant⁻¹)

include F in
lemma wilson_link(h:G.Simple)(hV:PostT C.path.levels)(hz:steep 𝓛 Z)(hp:(𝓛:Filter _)≤ X.fuse): Coupling G (wilson Z):=by
    let Z' i:= Z.β (glen C.S i); have he(i):0<Z' i:=measured hp F.room.cutoff hz _
    refine ⟨Eventually.of_forall fun x=>inv_pos.mpr (Real.sqrt_pos.mpr (he _)),?_⟩
    let A:= C.path.levels; let t:=glen C.S; let f:=fun i:ℝ=>A.clock.hatBeta (t i); have hx:= (gamut hp F.room.cutoff hz h).comp (glen_leads C.S); have hw:= (pace_log h hV).div hx (by norm_num); rw [div_one] at hw; exact hw.congr fun i=> by unfold wilson; rw [inv_pow,Real.sq_sqrt (he i).le]; change LogV i/f i/(Z' i/f i)=_; have hn:f i≠0:= (bell ..).ne'; field_simp [(bell A (t i)).ne', (he i).ne']

lemma Coupling.conforms(h:G.Simple){w:ℝ→ℝ}(hv:Coupling G w): Tendsto w trail (𝓝 0):=by
    have he:Tendsto LogV trail atTop:= Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have hh:= hv.running.div_atTop he; have hu:Tendsto (fun i=>w i^ (2:ℕ)) trail (𝓝 0):= hh.congr' ((he.eventually_gt_atTop 0).mono (fun i hi=>by dsimp only; field_simp));
    have hp:= hu.sqrt; rw [Real.sqrt_zero] at hp; exact hp.congr' (hv.positive.mono (fun i hi=>Real.sqrt_sq hi.le))
end YM.Trace.Pilot

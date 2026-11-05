import YM.TraceExtension.Atlas.Sink
import YM.TraceExtension.Atlas.Energy
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{J:Scaling S}{V:∀ i,Vane C i}{Z:Arch C}
variable (h₁:Scribe X J V Z F.sector 𝓛 F.room.kernel H)

-- global extension to position-frame prescription at each real length, not just subsequenced references.Through d=4.
structure Bliss (F: Final C X S)(𝓛:Ultrafilter (ℕ×ℕ))(Z:Arch C)(H:(Bel C.book).Hierarchy):Prop where
    lies : (𝓛:Filter _) ≤ X.fuse
    keen : steep 𝓛 Z
    budgets : PostT C.path.levels
    every : ∀ (J:Scaling S),StarPath X H J F.room.kernel 𝓛 → ∀ V Y,Gondola X H J 𝓛 V Y → Scribe X J V Z F.sector 𝓛 F.room.kernel H
    picks : ∀ (s:ℕ→ℝ), Tendsto s atTop (𝓝 0) → (∀ i,0 < s i) → ∃ f:ℕ→ℕ, StrictMono f ∧ ∃ J:Scaling S,J.r=s ∘ f ∧ ∃ V,Scribe X J V Z F.sector 𝓛 F.room.kernel H
lemma bliss(H:Gallery C X):∃ b Z H,Bliss F b Z H:=by obtain ⟨b,Z,H,hV,hz,hA,hs,hB⟩:=H.lead _ F.room F.sector F.phase.transport;exact ⟨b,Z,H,hV,hz,hA,hs,hB⟩

lemma contradictionTrail (P:ℝ→ Prop)(h:¬(∀ᶠ i in trail,P i)):∃ s:ℕ→ℝ,Tendsto s atTop trail∧∀ i,0 < s i∧¬P (s i):=by
   let d:= costHint; have he (i:ℕ):∃ s:ℝ,0<s ∧ s<d i ∧¬ P s:=by
      by_contra! hv; apply h;have hi : ∀ᶠ s:ℝ in trail, 0<s:=self_mem_nhdsWithin; filter_upwards[hi,(Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (show d i>0 from cost_pos i)))] with x hx hp; exact hv x hx hp
   choose s hs hp hE using he
   exact ⟨s,tendsto_nhdsWithin_iff.mpr ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun i=> (hs i).le) (fun i=>(hp i).le),Eventually.of_forall hs⟩,fun i=> ⟨hs _,hE _⟩⟩

def PlotX (F:Final C X S)(H:(Bel C.book).Hierarchy)(𝓛: Ultrafilter (ℕ×ℕ))(h:G.Simple)(p:ℝ→change S 4):= ∀ᶠ r in trail,AtAngle F (H:=H) (𝓛:=𝓛) h r (p r)
-- unselected profile X branch. All fixed sets eventually. Keep thru own horizon.
def chores (r:ℝ)(p:change S 4) (m:ℕ):Prop:= ∀ n:Fin (m+1), ∀ v: Fin n→ PegC C 4, ∀ j:Fin (m+1), ∀ x ∈ Scaling.window (sizeHint m) n,
      ‖iteratedFDeriv ℝ j (fun q=> S.classMoment S (fun _=>4) (r • q) (fun i=>p (PoleC C 4 (v i)))) x-iteratedFDeriv ℝ j (fun q=>(F₀).classMoment (F₀) (fun _=>4) q (fun i=>PoleC C 4 (v i))) x‖ ≤ costHint m
variable (hs:Bliss F 𝓛 Z H)
include hs
lemma glides (m:ℕ):∀ᶠ s in trail, ∃ p:change S 4,AtAngle F (H:=H) (𝓛:=𝓛) h s p∧∀ j : Fin (m+1),chores s p j:=by
    by_contra hd
    obtain ⟨s,hS,hQ⟩:= contradictionTrail _ hd; obtain ⟨f,hf,J,hJ,V,hV⟩:=hs.picks s (hS.mono_right nhdsWithin_le_nhds) (fun i=> (hQ i).1); obtain ⟨w,hw,hB⟩:=fulfill F h hV
    have hx(j:Fin (m+1)):∀ᶠ i in atTop, chores (J.r i) (w i) j:=by
       let W:=sizeHint j; have hp:0<W:=inv_pos.mp (cost_pos _)
       apply eventually_all.mpr; intro n; apply eventually_all.mpr;intro v; apply eventually_all.mpr; intro j'; exact weak_p F h hV w hw (fun i=>PoleC C 4 (v i)) j' _ (cost_pos _) _ (Next.UVStress.window_closed _ _) (fun x hx=>spaced_conf (inv_pos.mpr hp) hx.1)
    obtain ⟨i,hi,hσ⟩:= ((latium F h hV w hw hB).and (eventually_all.mpr hx)).exists; apply (hQ (f i)).2; rw[hJ] at hi hσ; exact ⟨w i,hi,hσ⟩
lemma glenned : ∃ p:ℝ→change S 4, PlotX F H 𝓛 h p∧∀ m:ℕ,∀ᶠ r in trail, chores r (p r) m:=by
    let U(r:ℝ)(f: change S 4)(m:ℕ):= AtAngle F (H:=H) (𝓛:=𝓛) h r f∧ ∀ j:Fin (m+1),chores r f j; let W(r:ℝ):= (Finset.range (glen C.S r+1)).filter (fun i=> ∃ p,U r p i)
    obtain ⟨x,X,hX⟩:= (glides F h hs 0).exists
    let R(r:ℝ):= if h:(W r).Nonempty then (show ∃ f,U r f ((W r).max' h) from (Finset.mem_filter.mp (Finset.max'_mem (W r) h)).2).choose else X
    have ht(m:ℕ):∀ᶠ r in trail,U r (R r) m:=by
        filter_upwards[glides F h hs m,(glen_leads C.S).eventually_ge_atTop m] with x hx hm; have hv:m ∈ W x:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm),hx⟩; have hQ:(W x).Nonempty:=⟨m,hv⟩
        let t:= (W x).max' hQ; have he: U x (R x) t:=by unfold R; rw[dif_pos hQ]; exact (show ∃ f,U x f t from (Finset.mem_filter.mp (Finset.max'_mem (W x) hQ)).2).choose_spec
        exact ⟨he.1,fun j=>he.2 (Fin.castLE (Nat.succ_le_succ (Finset.le_max' _ m hv)) j)⟩
    exact ⟨R,(ht 0).mono fun i hi=> hi.1,fun m=> (ht m).mono fun i hi=> hi.2 (Fin.last m)⟩

include hs
-- achieved leading coefficient at real lengths and any X scope. Scalar shows qstress identification afterward.
lemma s_color (P:ℝ→change S 4)(hp:PlotX F H 𝓛 h P): ∃ f:ℝ→ℝ, (∀ᶠ s in trail,s^ (4:ℕ) • lum F= (4*f s) • P s (stepField C)) ∧ ∀ g:ℝ→ℝ, Coupling G g→Tendsto (fun i=> f i / g i^ (2:ℕ)) trail (𝓝 (d2 G)):=by
    let T:=lum F;let t:= stepField C
    have hu:∀ᶠ i in trail,∃ d:ℝ,i^4 • T= (4*d) • P i t:=by
        filter_upwards[hp] with i hi; obtain ⟨c,hc⟩:= gardens F h _ hi.2 hs.every; refine ⟨-(i^ (4:ℕ)/(4*c)),?_⟩; rcases hc with ⟨hc,ht⟩;change P i t=_ at ht; rw[ht,smul_smul, smul_neg]; change _= -(_ • T); rw [← neg_smul]; congr 1; field_simp
    let F' (i:ℝ):=if h:∃ d:ℝ,i^(4:ℕ) • T=(4*d) • P i t then h.choose else 0; have ht:=hu.mono (fun i hi=> (show i^(4:ℕ) • T=(4*F' i) • P i t from by unfold F'; rw [dif_pos hi];exact hi.choose_spec))
    refine ⟨F',ht,fun g H'=>?_⟩
    rw[Filter.tendsto_def]; intro W hW; by_contra hu
    obtain ⟨s,hS,hQ⟩:= contradictionTrail _ hu
    obtain ⟨f,hf,J,hJ,V,hV⟩:= hs.picks s (hS.mono_right nhdsWithin_le_nhds) (fun i=> (hQ i).1);obtain ⟨U,hU,hX⟩:= fulfill F h hV
    have hp':Tendsto J.r atTop trail:= hJ ▸ hS.comp hf.tendsto_atTop
    obtain ⟨d,hD,hδ⟩:= vocal F h hV U hU hX
    have he:∀ᶠ i in atTop,F' (J.r i)=d i:=by
        filter_upwards [latium F h hV U hU hX,hδ,hp'.eventually ht,hp'.eventually hp] with i hi hh hu hm; have hs':=unique_v F h hV hs.every hm hi
        have hq: U i t≠0:=fun hz=> scale_alive h H ((U i).injective (hz.trans (map_zero _).symm)); have hv:= hu.symm.trans hh.2; rw[hs'] at hv; exact mul_left_cancel₀ (by norm_num : (4:ℝ) ≠ 0) (smul_left_injective ℝ hq hv)
    have hx:Tendsto (fun i=>BQ Z V i*g (J.r i)^2) atTop (𝓝 1):=by
        have hz: G.slopeConstant⁻¹≠0:= inv_ne_zero (Gauge.slopeConstant_pos h).ne'
        have hu:=(H'.running.comp hp').div hV.clock hz; rw[div_self hz] at hu; apply hu.congr'; filter_upwards [hV.clock.eventually_ne hz,hV.grows.eventually_gt_atTop 0] with i hi hp; let b:= BQ Z V i;let z:= LogZoom J i;change z*g (J.r i)^2/(z/b)= _; have hf:b≠0:= hp.ne'; have hb:z≠0:= (div_ne_zero_iff.mp hi).1; field_simp;rfl
    have hB:= hD.div hx one_ne_zero; rw[div_one] at hB
    obtain ⟨i,hi,hσ,hθ⟩:= ((hB.eventually hW).and (he.and (hV.grows.eventually_gt_atTop 0))).exists
    apply (hQ (f i)).2; change F' (s (f i))/g (s (f i))^2∈W; rw [← show J.r i=s (f i) from congr_fun hJ i,hσ]; change BQ Z V i*d i / (BQ Z V i*g (J.r i)^2) ∈ W at hi; rw [mul_div_mul_left _ _ hθ.ne'] at hi; exact hi
end YM.Trace.Pilot

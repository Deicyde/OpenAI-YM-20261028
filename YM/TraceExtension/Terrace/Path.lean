import YM.TraceExtension.Terrace.Gondola
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "a!"=> (𝓛:Filter (ℕ×ℕ))
local notation "A"=> C.path.levels
variable {Z:Arch C} (hZ:steep 𝓛 Z){d k i j:ℕ} {S:Table C.book}{X: Scaling S} {a : (Cells.standard C).Hierarchy}
local notation "T!"=> C.labels.level d
variable (H:C.Makes) (hb: (𝓛:Filter (ℕ×ℕ)) ≤ F.fuse)
variable {V:∀ i,Vane C i}{Y:∀ (d i:ℕ),(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola F a X 𝓛 V Y)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r D)
include hq hZ H hb
lemma floss (ht:d≤5)(hG:G.Simple)(v:(Cells.standard C).Field d)(hx:Cgrade (C.labels.level d) (Further.CorrectedLift.ladder C d v)): Tendsto (fun i=> let j:=(V i).k;(Z.β j*(X.r i)^d)⁻¹ • swale Z d j (Y d i v)) atTop (𝓝 ((C.labels.level d).core (Further.CorrectedLift.ladder C d v))):=by
   let Q i:= (V i).k; let t i:= Z.β (Q i)*(X.r i)^d; have ht'(i):0 < t i:= mul_pos (measured hb H hZ _) (pow_pos (X.positive _) _);
   let u:= (T!).core (Further.CorrectedLift.ladder C d v);
   let N':= (T!).coeffSize u; have hx':0 ≤ N':=Work.G08.size_nonneg ..
   have hE:Tendsto (fun i=> AgeK (A) (-(1/2:ℝ)) (Q i) *2 * N') atTop (𝓝 0):=by
      simpa only[zero_mul] using! (((Age_rate _ (a:=-(1/2)) (by norm_num) hG).comp hq.growth|>.mul_const 2).mul_const N')
   refine Metric.tendsto_nhds.mpr fun ε hp=> ?_
   filter_upwards [sky_tip hZ H hb hq d ht hG,hE.eventually (gt_mem_nhds hp)] with i hi hε
   let B':=swale Z d (Q i) (Y d i v); let c:= t i; have hc:0<c:=ht' i
   rw[dist_eq_norm]; change ‖c⁻¹ • B'-u‖<ε
   apply lt_of_le_of_lt _ hε; rw [show c⁻¹ • B'-u=c⁻¹ • (B'-c • u) from by rw[smul_sub,inv_smul_smul₀ hc.ne']]; refine (Push.RelayDifference.norm_cost (T!) _).trans ?_
   rw [count_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
   refine (mul_le_mul_of_nonneg_left (hi v hx) (inv_nonneg.mpr hc.le)).trans_eq ?_
   change c⁻¹*(_ *(2*c*N'))=_; field_simp; ring

omit hq hZ H hb in
private lemma rococo {d:ℕ}(f:Frame G d)(e:ℕ→ℝ) (v w : ℕ→f.Coeff)(p:f.Coeff)(hv:Tendsto v atTop (𝓝 p))(he:Tendsto e atTop (𝓝 0))(hp:∀ᶠ i in atTop,f.coeffSize (v i-w i) ≤ e i*f.coeffSize (w i)) : Tendsto w atTop (𝓝 p):=by
    have h(h:ℝ):Tendsto (fun i=> e i*(h*f.coeffSize (v i))) atTop (𝓝 0):=by simpa only[zero_mul] using! he.mul (((continu f).continuousAt.tendsto.comp hv).const_mul h)
    have hW:Tendsto (w-v) atTop (𝓝 0):=by
       apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply Metric.tendsto_nhds.mpr; intro ε hε
       filter_upwards [he.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)),hp,(h 2).eventually (gt_mem_nhds hε)] with i hi hp h'
       have hh:= f.coeffSize; let y:=f.coeffSize (v i-w i); let Q:=f.coeffSize (v i); let p:=f.coeffSize (w i); have H₀:0 ≤ p:= Work.G08.size_nonneg ..; have hQ:p ≤ 2*Q:=by
          have he := Work.G08.size_triangle f (w i) (v i);rw [Work.G08.size_sub_rev] at he; linarith only [he,hp,mul_le_mul_of_nonneg_right hi H₀]
       simp only[dist_zero_right,Real.norm_of_nonneg (norm_nonneg _),Pi.sub_apply,norm_sub_rev (w i)]
       by_cases ht:0≤ e i; · exact (lt_of_le_of_lt ((Push.RelayDifference.norm_cost f _).trans (hp.trans (mul_le_mul_of_nonneg_left hQ ht))) h')
       have hz:v i-w i=0:= Work.G08.size_separates f _ (hp.trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) H₀)); rw[hz,norm_zero]; exact hε
    exact (by simpa only[Pi.sub_apply,sub_add_cancel,zero_add] using hW.add hv)

def crown (Z:Arch C)(X:Scaling S) (Q:ℕ→ℕ)(d i:ℕ):= Z.β (Q i) * (X.r i)^d
def prize (Z:Arch C)(X: Scaling S)(V:∀ i,Vane C i) (d i:ℕ) : Module.End ℂ (C.label d):= (crown Z X (Stern V) d i)⁻¹ • swale Z d (Stern V i)
variable (K:Sceptre C W)(θ:PostT C.path.levels)(hG:G.Simple)
include θ hG
lemma stair_link (ht:d≤5)(v:(Cells.standard C).Field d)(hx:Cgrade (C.labels.level d) (Further.CorrectedLift.ladder C d v)) (hh:∀ᶠ i in atTop,let j:=(V i).k; let T:=C.labels.level d; let Y':=Y d i v; T.coeffSize (swale Z d j Y'-swale Z d (Stern V i) Y') ≤ part (A) j*T.coeffSize (swale Z d (Stern V i) Y')): Tendsto (fun i=> prize Z X V d i (Y d i v)) atTop (𝓝 ((C.labels.level d).core (Further.CorrectedLift.ladder C d v))):=by
    let f:= C.labels.level d; let t i:= (V i).k
    let b':= Z.β; let r:= (X.r); let u i:= (b' (t i)* (r i)^d)⁻¹; let Q(i):= f.core (Y d i v)
    let L(i):= u i • swale Z d (t i) (Y d i v); let M(i):=u i • swale Z d (Stern V i) (Y d i v)
    let p:= f.core (Further.CorrectedLift.ladder C d v); have ht': Tendsto M atTop (𝓝 p):=by
        refine rococo f (part (A) ∘ t) L M p (floss hZ H hb hq ht hG v hx) ((parts_rate _ hG).comp hq.growth) (hh.mono fun i h=>?_)
        unfold L M;rw [← smul_sub,count_smul,count_smul]; exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by rw [mul_left_comm]; rfl)
    have hb' : Tendsto (fun i=>b' (t i)/b' (Stern V i)) atTop (𝓝 1):= (Barry hZ H hb hG θ).comp hq.growth
    have hx := hb'.smul ht'; rw [one_smul] at hx; refine hx.congr (fun i=>?_)
    have hR :0<r i:=X.positive _; have hv :0 < b' (t i):= measured hb H hZ _; change _ • (u i • _)=_; rw [smul_smul]; change (b' (t i)/b' (Stern V i)* u i) • swale Z d (Stern V i) (Y d i v) =((crown Z X (Stern V) d i)⁻¹:ℝ) • swale Z d (Stern V i) (Y d i v)
    congr 1
    change b' (t i)/b' (Stern V i)*((b' (t i)*r i^d)⁻¹)= (b' (Stern V i)*r i^d)⁻¹; have hh:0 < b' (Stern V i):= measured hb H hZ _; field_simp
include K
lemma short_jig (v:(Cells.standard C).Field 4): Tendsto (fun i=>prize Z X V 4 i (Y 4 i v)) atTop (𝓝 ((C.labels.level 4).core (Further.CorrectedLift.ladder C 4 v))):=by
   refine stair_link hZ H hb hq θ hG (by decide) v (even_grade _ hG _) ?_
   filter_upwards [hq.growth.eventually (evening hZ hb K θ hG)] with i hi
   exact hi _ _ le_rfl (stellar ..|>.le)
include hr
lemma arrive_t (v : (Cells.standard C).Field 5)(hv : (Cells.standard C).mirror a.spin 5 archV v= -v): Tendsto (fun i=>prize Z X V 5 i (Y 5 i v)) atTop (𝓝 (Further.CorrectedLift.ladder C 5 v)):=by
   let f:=C.labels.level 5; let t:=Further.CorrectedLift.ladder C 5 v; have ht:night f t:=by
        have he:=ladder_spin a.spin archV v; rw[hv,map_neg] at he; exact he.symm
   change Tendsto _ _ (𝓝 t); rw [← nights _ ht]; refine stair_link hZ H hb hq θ hG (by decide) v (night_grade _ ht hG) ?_
   filter_upwards [hq.growth.eventually (nightsE hZ H hb hr K θ hG),(cruise hb hq 5)] with i hi h
   have hx:= (h v).2 archV; rw[hv,map_neg] at hx; exact hi _ _ (show night f (Y 5 i v) from hx.symm) le_rfl (stellar ..|>.le)
end YM.Trace.Terrace

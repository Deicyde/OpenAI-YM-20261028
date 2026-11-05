import YM.TraceExtension.Terrace.Vector
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux
open Further.PhysicalPeriodLimitF933
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "U#"=> C.labels.level 5
local notation "A"=> C.path.levels
variable {Z:Arch C} (hZ:steep 𝓛 Z) {S:Table C.book}{X:Scaling S} {i d j:ℕ}
variable (H:C.Makes) (hb:(𝓛:Filter (ℕ×ℕ)) ≤ F.fuse)
local notation "T!"=>C.labels.level d
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r D)
include hZ H hb hr
lemma prismatic {a:ℝ}(hj: C.ref d ≤ j)(x:C.label d) (s:Signed): booty Z d j a ((T!).act s.ortho x)=(T!).act s.ortho (booty Z d j a x) ∧ booty Z d j a (star x)=star (booty Z d j a x):=by
    let Q:= Z.M d j
    have he : (Z.M d j).symm ((T!).act s.ortho x)= (T!).act s.ortho (Q.symm x):= (Z.M d j).injective (by rw[move_anchor hZ H hb hr hj,LinearEquiv.apply_symm_apply,show Z.M d j (Q.symm x)=_ from Q.apply_symm_apply x])
    have hf : (Z.M d j).symm (star x)=star (Q.symm x):=(Z.M d j).injective (by rw [move_anchor_star hZ H hb hr hj,LinearEquiv.apply_symm_apply,show Z.M d j (Q.symm x)=_ from Q.apply_symm_apply x]);
    simp_rw[treasure]; rw[he,hf]; exact ⟨(((T!).act s.ortho).restrictScalars ℝ|>.map_smul ..).symm, ((reflB (T!)).map_smul ..).symm⟩
lemma fisc (hj:C.ref 5 ≤ j)(v:C.label 5)(hv:night (C.labels.level 5) v)(a:ℝ): Vault S Z 5 j a (swale Z 5 j v)= a • S.project 5 v:=by rw[cash_pin, nights (C.labels.level 5) (gateW hZ H hb hr hj v hv),LinearEquiv.symm_apply_apply]
omit hZ H hb hr
structure Spun (Z:Arch C)(X:Scaling S)(V:∀ i,Vane C i)(a:(Cells.standard C).Hierarchy)(s:ℕ→ Bowl (C.labels.level 5) →L[ℝ] (TableOne a.spin)) : Prop where
    starts: ∀ᶠ i in atTop,∀ v d, (s i v).val d=(X.U i 5).symm (Vault S Z 5 (Stern V i) (crown Z X (Stern V) 5 i) (v.val d))

variable {V:∀ i,Vane C i}{Y:∀ (d i:ℕ),(Cells.standard C).Field d→L[ℂ] C.label d}{a:(Cells.standard C).Hierarchy} (HS:S.Hierarchy) (hs:StarPath F a X HS 𝓛)
variable (hq:Gondola F a X 𝓛 V Y)
include hZ H hb hr hs hq
lemma gazes : ∃ s:ℕ → Bowl (C.labels.level 5) →L[ℝ] (TableOne a.spin), Spun Z X V a s:=by
    let D:= (U#); let Q:= Stern V; let u i:=Vault S Z 5 (Q i) (crown Z X (Stern V) 5 i); let Y(i):C.label 5 →ₗ[ℂ] (Cells.standard C).Field 5:= (X.U i 5).symm.toLinearMap.comp (u i)
    let P (i:ℕ)(f:Bowl D →ₗ[ℝ] TableOne a.spin):Prop:=∀ v d,(f v).val d=(X.U i 5).symm (u i (v.val d))
    have he:∀ᶠ i in atTop,∃ f,P i f:=by
        filter_upwards [hq.growth.eventually ((Sstar (A)).eventually_ge_atTop (C.ref 5)),hs.units 5] with i ht hi
        have hξ(t:C.label 5)(s:Signed):u i (D.act s.ortho t)= S.mirror HS.spin 5 s (u i t):=by
            unfold u Vault; simp only [LinearMap.comp_apply,Table.mirror_project] ;
            exact congr_arg (S.project 5) ((prismatic hZ H hb hr ht t s).1)
        have hh(t:C.label 5): u i (star t)=S.conj HS.spin 5 (u i t):=by unfold u Vault; simp only [LinearMap.comp_apply,Table.conj_project]; exact congr_arg (S.project 5) ((prismatic hZ H hb hr ht t 1).2)
        let f:= vectorMap (K:=reflA D) (D:=spinQ a.spin) (R:=reflB D) (T:=conjQ a.spin) ((Y i).restrictScalars ℝ) (show ∀ s x,(X.U i 5).symm (u i (D.act s.ortho x))= (Cells.standard C).mirror a.spin 5 s (Y i x) from fun s x=> by rw [hξ]; exact (flips hi.1).signed ..) (fun x=>by change (X.U i 5).symm (u i (star x))=(Cells.standard C).conj a.spin 5 _; rw[hh]; exact (flips hi.1).stars ..)
        exact ⟨f,fun _ _=>rfl⟩
    let f i:= if h:∃ f,P i f then Classical.choose h else 0
    refine ⟨fun i=>LinearMap.toContinuousLinearMap (f i),⟨?_⟩⟩; filter_upwards[he] with i hi; exact (show P i (f i) from by unfold f; rw[dif_pos hi]; exact Classical.choose_spec hi)

-- section sent out from station's issued coefficients. No new X.
variable {s:ℕ → Bowl (C.labels.level 5) →L[ℝ] (TableOne a.spin)}
variable (K:Sceptre C W)(θ:PostT C.path.levels)(hG:G.Simple) (hp: Spun Z X V a s)
include K θ hG hp
omit hs HS in
lemma lensP : ∃ (U:TableOne a.spin→ₗ[ℝ] Bowl (C.labels.level 5))(t:ℕ→ TableOne a.spin→ₗ[ℝ] Bowl (C.labels.level 5)),
       (∀ w,Vbase a.spin (U w)=w) ∧(∀ w,Tendsto (fun i=>t i w) atTop (𝓝 (U w))) ∧ ∀ᶠ i in atTop,∀ v:TableOne a.spin, s i (t i v)=v:=by
    let F':= (U#); let P(i)(t: TableOne a.spin→ₗ[ℝ] Bowl F') := ∀ v:TableOne a.spin, s i (t v)=v ∧ ∀ d,(t v).val d=prize Z X V 5 i (Y 5 i (v.val d))
    obtain ⟨U,hU⟩:=section5 a.spin
    have he:∀ᶠ i in atTop,∃ t,P i t:=by
       filter_upwards [hp.starts,hq.terminal 5,hq.growth.eventually ((Sstar (A)).eventually_ge_atTop (C.ref 5)),cruise hb hq 5] with i hi ht hx hK
       let M':= Y 5 i; let R: Module.End ℂ (C.label 5):= prize Z X V 5 i
       let y:= crown Z X (Stern V) 5 i; let Q:= swale Z 5 (Stern V i); let u:=Vault S Z 5 (Stern V i) y
       have hy:0<y:= mul_pos (measured hb H hZ _) (pow_pos (X.positive i) _);
       change C.ref 5 ≤ (Stern V i) at hx
       -- M' maps into Bowl; Q via night =& whole M times θ. only on Bowl.
       let f:=vectorMap (K:=spinQ a.spin) (R:=conjQ a.spin) (D:=reflA F') (T:=reflB F') (M'.toLinearMap.restrictScalars ℝ) (fun s x=> (hK x).2 s) (fun x=> (hK x).1)
       let b:= (((A).budget (Stern V i)).threshold)^2; let N:= y⁻¹ • (b⁻¹ • (Z.M 5 (Stern V i)).toLinearMap)
       have hξ(v:Bowl F')(j:Axis): N (v.val j)= R (v.val j):= by
           change y⁻¹ • (b⁻¹ • _)=y⁻¹ • swale _ _ _ _; rw [land,nights F' (gateW hZ H hb hr hx (v.val j) (frames_night F' v j))];rfl
       have hw(s x):N (reflA F' s x)=reflA F' s (N x):=by simp only [N,LinearMap.smul_apply, LinearEquiv.coe_coe,map_smul]; change _= y⁻¹ • (b⁻¹ • (F'.act s.ortho _)); exact congr_arg _ (congr_arg _ (move_anchor hZ H hb hr hx x s))
       let z:= vectorMap (N.restrictScalars ℝ) (K:=reflA F') (R:=reflB F') (D:=reflA F') (T:=reflB F') hw (fun x=>by change y⁻¹ • (b⁻¹ • Z.M 5 (Stern V i) (star x))=_; rw[move_anchor_star hZ H hb hr hx]; exact (by change _=reflB F' (y⁻¹ • (b⁻¹ • Z.M 5 (Stern V i) x)); rw[map_smul,map_smul];rfl))
       refine ⟨z.comp f,fun v=>?_⟩
       have he(d): (z (f v)).val d=R (M' (v.val d)):= hξ (f v) d
       refine ⟨Subtype.ext ?_,he⟩; funext d; rw [hi]; change _=v.val d; let k:= (Stern V i)
       change (X.U i 5).symm (u ((z (f v)).val d))=_; rw[he]; change (X.U i 5).symm (u (y⁻¹ • Q _))= _; rw[show ∀ v:C.label 5,u (y⁻¹ • v)=y⁻¹ • u v from fun _=>(u.restrictScalars ℝ).map_smul .., show u (Q _)=_ from fisc hZ H hb hr hx (M' (v.val d)) (frames_night F' (f v) d) y,inv_smul_smul₀ hy.ne', show S.project 5 (M' (v.val d))= _ from (ht.2 (v.val d)).symm,LinearEquiv.symm_apply_apply];
    let t i:= if h:∃ t,P i t then Classical.choose h else 0
    have ht:∀ᶠ i in atTop,P i (t i):= he.mono fun i hi=>by unfold t; rw [dif_pos hi]; exact Classical.choose_spec hi
    refine ⟨U,t,fun v=> (hU v).1, fun v=> ?_, ht.mono fun i h v=>(h v).1⟩
    refine tendsto_subtype_rng.mpr <| tendsto_pi_nhds.mpr fun i=> ?_
    have hΩ:= arrive_t hZ H hb hq hr K θ hG (v.val i) (vspin a.spin v i)
    rw [← (hU v).2 i] at hΩ; refine hΩ.congr' ?_; exact ht.mono fun j hj=> ((hj v).2 i).symm
end YM.Trace.Terrace

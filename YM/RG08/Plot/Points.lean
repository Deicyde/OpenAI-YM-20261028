import YM.RG08.Plot.Tribute
/-!
# Testing and gathering call on full product profile before interpretation
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff Classical
variable {I α E:Type}{i K D h τ e r k L:ℕ}{z:Cover}{c A η σ R:ℝ}{x:E4}{G:Gauge}{X:Chain}
section kinematics
-- These are per-root germs of the insertion submitted at its native level $i$. Sum against physical profile before receiving.
def tariff (h:ℕ)(q:ℝ):= q^4/q^h
variable {U:BoardU D R G}
def unitA (X:Chain)(h K i:ℕ)(f: Exam D)(x:E4)(U:BoardU D R G)(z:Cover): Tale G := tariff h (spanP X K i) • ringU (exteriorP f (spanP X K i) x z) U
def stemU (X:Chain)(h K i:ℕ)(f: Exam D)(x:E4)(U:BoardU D R G)(z:Cover) : Tale G:= Town.season z (unitA X h K i f x U z)
def collect (X:Chain)(h K i:ℕ)(f:Profile D)(x:E4)(U:BoardU D R G):Tale G:= ∑ z∈blush f X K i x R, stemU X h K i f.val x U z
-- keeps roots ALL, even when large and h valuation positive. Native Φ cost exposed.
lemma owed (g:Profile D)(hz:z ∉ blush g X K i x R): unitA X h K i g.val x U z=0 := by
   unfold unitA; rw [show ringU (exteriorP g.val _ _ z) U=0 from ?_,smul_zero]
   funext i j u; exact no_exam (mt blush_v.mpr hz) _
lemma charge_t (f:Exam D)(x:E4)(k i:ℕ)(hv:Marvel τ U)(d:ℕ) (X:Chain)(z:Cover): Stone τ (unitA X d k i f x U z):= (Stone.graph hv _).weight _
lemma stem_for (g:Profile D)(x:E4)(h K i:ℕ)(hv:Marvel τ U): Stone τ (collect X h K i g x U):= Stone.group _ _ (fun v _=> (charge_t g.val x K i hv h X v).transport _)
@[simp] lemma season_z {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x:Cover): Town.season x (0:Screed E α)=0:= rfl
lemma season_group (s:Finset I){u: I→ Tale G}: Town.season z (∑ i∈s,u i)=∑ i∈s, Town.season z (u i):= by
   funext i j; simp only [Town.season,Finset.sum_apply,Town.roam_group]
lemma season_c (x y:Cover){V:Tale G}: Town.season x (Town.season y V)=Town.season (x+y) V:= by
   funext i j p; change V i j (shiftedBy (-y) (shiftedBy (-x) p))= V i j (shiftedBy (-(x+y)) p); congr 1; funext i; simp [shiftedBy,sub_eq_add_neg,add_left_comm,add_comm,add_assoc]
lemma season_scale (w:Cover)(v:ℝ){P:Tale G}: Town.season w (v•P)=v • Town.season w P:= rfl
-- gather test physically, mass correspondence. No chart pol approximations needed.
lemma occurs {f:Profile D}{P:StripU G (X.S.block i)} (hp:1/2≤R)(hv:Marvel τ U)(hk:Fair P) : inscribed τ P 0 (collect X h K (i+1) f x U)= collect X h K i f x (Needle.push P τ h U):= by
   let g:=f.val; let L:= X.S.block i; let v:=spanP X K i; let w:=spanP X K (i+1); let W (v:Cover)(p:Site L):= stemA L v p
   let F a:= unitA X h K (i+1) g x U a; let G' a:= stemU X h K (i+1) g x U a
   let Q':= Needle.push P τ h U; let H a:=unitA X h K i g x Q' a; let G a:=stemU X h K i g x Q' a
   let V:=blush f X K i x R; let C:=blush f X K (i+1) x R; let B:= (V ×ˢ (Finset.univ: Finset (Site L))).image fun p=> stemA L p.1 p.2
   have hC : C ⊆ B:= fun p hz=> by
      apply mem_image.mpr; let z:=growP L p; have ht:= descendant hp (blush_v.mp hz); exact ⟨(z,growL L p),mem_product.mpr ⟨blush_v.mpr ht,mem_univ _⟩,grows ..⟩
   have hz z: Stone τ (F z):= charge_t g x K (i+1) hv h X z
   have hj : (∑ z∈C,G' z)=(∑ z∈ B,G' z) := Finset.sum_subset hC fun i hi h'=>by unfold G' stemU; rw [owed f h']; rfl
   change inscribed τ P 0 (∑ z∈C,G' z)=∑ z∈ V,G z
   rw [hj, inscript_list B _ G' (fun i _=> (hz i).transport _) hk]
   have hk' : Function.Injective (fun p:Cover×Site L=> stemA L p.1 p.2):= fun u v h=> by
     have h1:=congr_arg (growP L) h; have h2:=congr_arg (growL L) h
     exact Prod.ext ((stemA_fit L u|>.1).symm.trans (h1.trans (stemA_fit L v|>.1))) ((stemA_fit L u|>.2).symm.trans (h2.trans (stemA_fit L v|>.2)))
   rw [Finset.sum_image (fun _ _ _ _ h=>hk' h),Finset.sum_product]; refine Finset.sum_congr rfl ?_
   intro z hφ; dsimp only
   let p0:= tariff h v; let p1:=tariff h w; let t:= (↑L.val:ℝ)^h/(Fintype.card (Site L):ℝ); have hp':p0*t = p1:= by
     have he: v=w*L.val:= (spanP_tick X K i|>.symm); have hL:0<w:=spanP_pos ..; unfold p0 p1 t tariff; rw [he,Lattice.site_card]; push_cast; field_simp; ring
   let φ:= exteriorP g v x z; let ψ (i:Site L):=Pages.roll (spinner i) (L.val:ℝ)⁻¹ φ
   have he i: ψ i=exteriorP g w x (W z i):= retest (spanP_tick X K _|>.symm) i _ z
   have hT : G z= Town.season z (p1 • ∑ p:Site L, inscribed τ P p (ringU (ψ p) U)):= by
       change Town.season z (p0 • ringU φ (Needle.push P τ h U))=_
       rw [anthem φ hp hk hv,smul_smul, show (↑(X.S.block i).val:ℝ)^h/(Fintype.card (Site (X.S.block i)):ℝ)=t from rfl, hp']
   rw [hT,Finset.smul_sum,season_group]; apply sum_congr rfl; intro i hi; rw [← inscription_sc i p1 (Stone.graph hv _) hk, he]
   exact order_moves (p:=i) (hz _) hk (by rw [nil_root]; unfold stemA; rw [zero_add])
lemma move_collect (p:Profile D) (x:E4)(X:Chain)(U:BoardU D R G)(h K i:ℕ): Town.season (-arcT X K i x) (collect X h K i p x U)= ∑ z∈ blush p X K i x R, Town.season (z-arcT X K i x) (unitA X h K i p.val x U z):= by
   unfold collect stemU; rw [season_group]; exact Finset.sum_congr rfl fun j hj=> by rw [season_c, add_comm _ j,sub_eq_add_neg]
end kinematics
end YM.RG08.Plot

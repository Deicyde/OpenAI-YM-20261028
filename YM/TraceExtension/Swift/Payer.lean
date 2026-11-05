import YM.TraceExtension.Swift.Happiness
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{k m:ℕ}{A c:ℝ}
lemma pulseB(S:Stage)(m:ℕ)(h:1  ≤ m)(A:ℝ)(ha:1 ≤ A): ∀ᶠ x:ℝ in atTop, kettle m*(peace x/sash S x) ≤ A ∧ zeff (shear x) A (sash S x)*(kettle m*(peace x/sash S x)) ≤ 1:=by
    let f(x):= zeff (shear x) A (sash S x); let D:= kettle m; have hD:0<D:=Outer.Nodes.loc_pos m
    have hh(F:ℝ→ℝ)(p:ℝ)(hp:ConstMass p F) :∀ᶠ x:ℝ in atTop,F x*(peace x/sash S x) ≤ 1:=by
       filter_upwards [hp (p+1) (lt_add_one _), wave_sub (p+1) (1/24) (by norm_num),eventually_gt_atTop (1:ℝ)] with x hx hv hy; obtain ⟨ht,hq,hH⟩:= pet x hy.le S; refine (mul_le_mul (hx.2.trans hv) hH (div_nonneg hq.le ht.le) (by positivity)).trans_eq ?_; rw[Real.rpow_neg (by positivity), mul_inv_cancel₀ (by positivity)]
    filter_upwards [hh (fun _=>D) 0 (mass hD.le), hh (fun x=>D*f x) 4 ((qr 0 m S h A ha).times D hD.le)] with x hx hv; refine ⟨hx.trans ha,(le_of_eq (show f x*_=(D*f x)*(peace x/sash S x) from ?_)).trans hv⟩; unfold f D; ring
lemma pieceK (m k:ℕ)(K A C:ℝ)(hk:0 ≤ K)(ha:1 ≤ A)(hm:48 ≤ m)(hc:0≤ C)(G:Gauge)(S:Stage): ∀ᶠ x:ℝ in atTop,∀ n:Side, tides (G:=G) m (orbAmt K (thinM x) (shear x) A (sash S x) C (k+m+1)) (peace x) (sash S x) (ExtS n x) ≤ swole x * peace x:=by
   let F(x):=zeff (shear x) A (sash S x); let V:=k+m+1; let Q(x):=composeCost V C (F x); obtain ⟨v,hv,H⟩:= bears m k A C S ha hc (by omega)
   let f(x:ℝ):=(((high x+high x+1)^4:ℕ)* Fintype.card (Loc G 1):ℕ)*(2^V*(K*thinM x)*Q x)*tome m
   have ht: ∃ a,ConstMass a f:=by
      have h1:= ((((expansion.gather expansion).gather (mass zero_le_one)).crop 4).cop (mass (Nat.cast_nonneg (Fintype.card (Loc G 1))))); have h2:= (mass (show 0 ≤ (2:ℝ)^V by positivity)).prod ((mass hk).prod (waveM (1/200)))
      unfold f; push_cast; exact ⟨_,((h1.prod (h2.prod H)).prod (mass (tome0 m)))⟩
   obtain ⟨a,h0⟩:=ht
   filter_upwards [H _ (lt_add_one v),pledge m f S 0 _ a hk h0 hm,eventually_gt_atTop (1:ℝ)] with x hx hh hv n
   obtain ⟨hp,hp',h⟩:= pet x hv.le S; refine le_trans ?_ hh; unfold f ; apply le_trans (b:= (↑((((high x+high x+1)^4:ℕ)*Fintype.card (Loc G 1):ℕ)):ℝ) * (tome m*orbAmt K (thinM x) (shear x) A (sash S x) C (k+m+1)*(peace x/sash S x)^(m+1))) ?_ (le_of_eq ?_)
   · have hp₀:0≤thinM x:=(Zn.wake ..).le; have hh:0 ≤ composeCost V C (zeff (shear x) A (sash S x)):=hx.1
     apply mul_le_mul_of_nonneg_right _ (by unfold orbAmt; exact mul_nonneg (mul_nonneg (tome0 m) (mul_nonneg (by positivity) hh)) (by positivity))
     exact Nat.cast_le.mpr (Nat.mul_le_mul_right _ (le_trans (Corona.halo_size ..) (by simp)))
   unfold orbAmt Q F V; ring
-- common core.S.Frame.E estimates stage
structure Castle (m k:ℕ)(Y:Gal G n)(F:Peat G n)(v:ℝ)(R:RG.Rep G n) (S:Stage)(C A:ℝ):Prop where
   reg(P:Support n) : ExtS n v ⊆ P→R.p.Regular P (atuneU m Y F (peace v) (ExtS n v))
   sea (o:Bond n)(x:G.Color) :‖x‖≤1→Spells G A C k m o x (sash S v) (peace v) (shear v) F
   pay (x: Directions G n): ‖x‖ ≤ A → Through k (minor (atuneU m Y F (peace v) (ExtS n v)) (sash S v)) x (swole v*peace v)
lemma bravo (m k:ℕ) (hm:48 ≤ m)(A:ℝ)(ha:1 ≤ A)(G:Gauge)(hG:G.Simple)(S:Stage) : ∃ Z C:ℝ,0 ≤ Z ∧ 0 ≤ C ∧ ∀ᶠ x:ℝ in atTop,∀ (n:Side) (R:RG.Rep G n) (Y:Gal G n)(F:Peat G n),
    let L:=k+m+1; Splendor F (ExtS n x) L (shear x) C → Drift _ F→ Clouded Y (ExtS n x) → Climate Y L (thinM x) C → Castle m k Y F x R S Z A:=by
   obtain ⟨C,T,D,hC,hT,hD,H⟩:= brill G A ha k m (by omega)
   let Z:= S; refine ⟨D,C,hD,hC,?_⟩
   filter_upwards [eventually_gt_atTop (1:ℝ), pulseB S m (by omega) A ha, pieceK m k T A D (by positivity) ha hm hD G S, sash_ok S _ zero_lt_one] with x hx hp hQ hr n R Y F L ht hz hW hY
   obtain ⟨hv,he,hh⟩:= pet x hx.le S; have hV:0≤ thinM x:=(Zn.wake ..).le; have hw:0≤ shear x:=by unfold shear; positivity [hx,hV,show 0<wideM x from Zn.wake ..]
   let H'(o:Bond n)(v:G.Color)(h:‖v‖≤ 1):= H n (ExtS n x) F Y (sash S x) (peace x) (shear x) (thinM x) o v h hw hV hv hr he hp.1 hp.2 (by exact hW.rises.2) hY ht
   exact ⟨fun P h=> lantern m (peace x) hz hW ht.locale ht.symm R.p h,fun o v h=>(H' o v h).1,fun z hv'=> (heaps m R.p (show 1  ≤ m by omega) hv he hz hW (fun o _ v h=> (H' o v h).2) z hv').mono (hQ n)⟩
end YM.Trace.Swift

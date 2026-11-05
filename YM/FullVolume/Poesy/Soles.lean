import YM.FullVolume.Poesy.Nocturne
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
open Yard Ovens Ovens.Pipes
namespace Angel
variable {ι:Type}{F T:ℕ→ι→ Config G c→ℝ}
lemma star (h:Angel F T) (u:ι)(V:ℕ→ Config G c) :Tendsto (fun n=> F n u (V n)-T n u (V n)) atTop (𝓝 0):=by
   refine Metric.tendsto_nhds.mpr fun i hi=>?_ ; filter_upwards [h.sails u _ (half_pos hi)] with n hn; rw [dist_zero_right]; exact lt_of_le_of_lt (hn (V n)) (half_lt_self hi)
lemma glints (h:Angel F T) (hJ:(J:Filter ℕ) ≤ atTop)(i:ι)(V:ℕ→ Config G c): Glints J (fun n=> F n i (V n)) (fun n=> T n i (V n)):=by
     obtain ⟨w,hw,H⟩:= h.a.sup; refine Glints.time ?_ ((star h i V).mono_left hJ); obtain ⟨b,hb⟩:=hw.bound
     exact FullVolume.Shadow.flowers (x:=0) (b:=b) (f:=fun n=>F n i (V n)) (Eventually.of_forall fun n=>by rw [dist_zero_right]; exact (H ..).trans (budget_single (hb n) i))
private lemma wages {x y B:ℝ} (he: |x|≤y) (hy:y≤B): ‖Real.exp x-1‖ ≤ y*Real.exp B :=by
   suffices h : ‖Real.exp x- Real.exp 0‖≤ Real.exp B*‖x‖ by rw [Real.exp_zero] at h; rw [mul_comm y]; exact h.trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
   let s:=Set.Icc (-B) B; have hv:= he.trans hy; have hp:0 ≤ B:= (abs_nonneg _).trans hv; have hs : x∈s:=abs_le.mp hv
   have hk:= Convex.norm_image_sub_le_of_norm_deriv_le (s:=s) (f:=Real.exp) (C:=Real.exp B) (fun x hx=> Real.differentiableAt_exp) (fun i (hi : i∈s)=>by simp only [Real.deriv_exp]; rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone hi.2) (convex_Icc ..) (show (0:ℝ)∈s from ⟨by linarith,hp⟩) hs
   simpa only [sub_zero] using hk
lemma rings (h:Angel F T): Angel (fun n i U=> Real.exp (F n i U)-1) (fun n i U=> Real.exp (T n i U)-1):=by
   have hk (F:ℕ→ι→ Config G c→ℝ) (h:Vented F):Vented (fun n i U=> Real.exp (F n i U)-1):=by
       obtain ⟨v,hv,V⟩:=h.sup; obtain ⟨p,hp⟩:= hv.bound; exact ⟨_,hv.climb (Real.exp_pos p).le,fun n u i=> (wages (V ..) (budget_single (hp n) i)).trans_eq (mul_comm ..)⟩
   refine ⟨hk F h.a,hk T h.b,fun i b hv=> recover (F:=fun n u=>_) (H:=fun n u=> _) (fun V=> ?_) b hv⟩; refine (tendsto_iff_ultrafilter ..).mpr fun J hj=> ((h.glints hj i V).bin (Q:=fun x=> Real.exp x-1) (fun _ _=> (Real.continuous_exp.sub continuous_const).continuousAt)).shrank
lemma herb (B:BudgetPoint) (A : Pipes G c) {D D':ℕ→ Tap G c} (h:Angel (fun n=> (D n).forced) (fun n=>(D' n).forced)) (hp:Angel (fun n=>(D n).logarithm) (fun n=>(D' n).logarithm))(P:ℕ≃ A.Pellet): Angel (fun n=> Pipes.solid P B (D n)) (fun n=> Pipes.solid P B (D' n)):=by
    let f n:= Pipes.reach (D n); let g n:= Pipes.reach (D' n); have hk :Angel f g:= Angel.both h hp.rings
    let V:= P.toEmbedding.trans (Embedding.subtype _); have H(D:ℕ→ Tap G c)(h:Vented fun n=> Pipes.reach (D n)):Vented fun n=> Pipes.solid P B (D n):=by
         obtain ⟨w,hw,W⟩:=h.sup; have hh:=hw.arbitrary.pull V; refine ⟨_,hh,fun n u i=>?_⟩; unfold Pipes.solid; split; next ht=> rw [norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) fun _ _=> W ..
         rw [norm_zero]; exact hh.value ..
    refine ⟨H D hk.a,H D' hk.b,fun i b he=> recover (F:=fun n=> Pipes.solid P B (D n) i) (H:=fun n=> Pipes.solid P B (D' n) i) (fun V=>?_) b he⟩
    refine (tendsto_iff_ultrafilter ..).mpr fun J hj=>?_
    exact Glints.shrank (switch ((Frill.pears (P i).val fun x _=> Frill.bare (hk.glints hj x V) (x:=(0:ℝ)) (n:=0)).crest) ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=> (addr P B i).eligible B.threshold (V n)))
end Angel
open Slide Marlin
lemma reno (B:BudgetPoint)(A: Listing G c) (k z:ℕ)(V V':ℕ→Trio.Offer G c)(f g: ℕ→ Trio.Offer G c) {D D':ℕ→ Collection.Source G c}(h:Canopy B A.reg (fun n=>(D n).logRead) (fun n=>(D' n).logRead))(hh: Angel (fun n=>(D n).hardRead) (fun n=> (D' n).hardRead))(hv:Canopy B (Marlin.leap k) V V')(ht:Angel f g) : let Z:= lodge A k z; let F n:= poursP B Z (bison (D n) (V n) (f n)); let G n:= poursP B Z (bison (D' n) (V' n) (g n)); Canopy B (Marlin.pluck B Z).reg (fun n=>(F n).logRead) (fun n=>(G n).logRead)∧ Angel (fun n=>(F n).hardRead) (fun n=> (G n).hardRead):=by
    intro X F H; let G':= G; let W:= Sum.elim A.reg (sea k (c:=c)); let u n:= Sum.elim (D n).logRead (choir (V n)); let v n:=Sum.elim (D' n).logRead (choir (V' n)); have hs :Canopy B W u v:= Canopy.splices h (laurels hv)
    let d(n):= bison (D n) (V n) (f n); let d' n:= bison (D' n) (V' n) (g n); let f' n (i:Civ c):= Sum.elim (fun _=> (0:Config G c→ℝ)) (choir (-f n)) i; let g' n(i:Civ c):= Sum.elim (fun _=> (0:Config G c→ℝ)) (choir (-g n)) i
    have hl :Angel f' g':=by
         apply Angel.both Angel.empty
         have hx {P:ℕ→ Site c→ Config G c→ℝ}(h:Vented P):Vented (fun i=> choir (-P i)) :=by
             obtain ⟨w,hw,W⟩:=h.sup; refine ⟨_,(trep (ι:=Seat c) hw).climb (Song.rim_nn c),fun n v x=> ?_⟩
             unfold choir; dsimp only [Pi.smul_apply, Pi.neg_apply]; rw [norm_smul, Real.norm_of_nonneg (Song.rim_nn c)]; simp only [Function.comp_apply, Pi.neg_apply,norm_neg]; exact mul_le_mul_of_nonneg_left (W ..) (Song.rim_nn c)
         refine ⟨hx ht.a,hx ht.b,fun ⟨i,x⟩ b hb=>recover (F:=fun n=>f' n (.inr (i,x))) (H:=fun n=> g' n (.inr (i,x))) (fun V=>?_) b hb⟩
         exact (tendsto_iff_ultrafilter ..).mpr fun J hj=> ((ht.glints hj x (fun n=>i.view (V n))).bin (Q:=fun x:ℝ=> Song.Rim c* (-x)) (fun _ _=>continuousAt_const.mul continuousAt_id.neg)).shrank
    exact ⟨hs.transI (leanU c).toEmbedding, Angel.herb B X (D:=d) (D':=d') hh (hl.forms (leanU c).toEmbedding) (hak X)⟩
end YM.ConnectedActivityE6.Lim

import YM.FullVolume.E6.Steels
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
open Pressure.Stores Tags
namespace Draft
variable (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin)(H₁:∀ n,Cash W x μ L Q o C₀ (H n).tubes (H n).kin)(hQ:∀ n, Promo Q o j x v ℓ a Z.χ (K n).tubes)
   (hz:Z.Paid Q o x) (h:Finish J K H)(hv:0≤v)
   (U₀:ℕ→ Config G c)(he:∀ᶠ i in (J:Filter ℕ), Z.Viable (U₀ i))
set_option quotPrecheck false
local notation "D"=> fun n => Z.paints (K n) (U₀ n)
local notation "D'"=> fun n=> Z.paints (H n) (U₀ n)
local notation "Hn" => (fun n (_:ℝ)=>U₀ n)
include hz H₀
lemma current (w:Air f G) : ∀ᶠ i in (J:Filter ℕ), Z.Viable (U₀ i)→ (D i).liftA ((K i).beta) (kickback (D i) ((K i).beta) w)=(D i).atmos w:= Eventually.of_forall fun i hi=> (Vine.shine (D i) (hz.1.symm ▸ (H₀ i).laws.data.room) hi _ _).trans (kickback_home _ (H₀ i).laws.intake.positive _)
local notation "z"=>radiusB Z.x
include hv h H₁ hQ he
lemma rawAge (u:Directions G f)(i: Raw.LogLetter c f) : Glints J (fun n=> (D n).inhale (K n).kin o.a u i) (fun n=> (D' n).inhale (H n).kin o.a u i):=by
    let α:=(D 0).enforce (2*o.a) u ((D 0).plaza (Raw.space (K 0).tubes 0 z (K 0).kin i))
    let V n:= (D n).input u; let C i n:= expo (K n).tubes Z.x (K n).kin (V n) (U₀ n) i; let M i n:=expo (H n).tubes Z.x (H n).kin (V n) (U₀ n) i
    have hh : Glints J (C i) (M i):=by
        let U' (n:ℕ)(_y:ℝ):=U₀ n; have hz:=h.ridge (j:=0) (U:=U') (p:=0) (Quincy.standards _ U₀) V Z.x
        rcases i with i|i|i|i|i|i
        · exact (hz (.inl i)).crest
        · exact (hz (.inr (.inl i))).crest
        · exact (hz (.inr (.inr (.inl i)))).crest
        · exact (hz (.inr (.inr (.inr (.inl i))))).crest
        · exact (hz (.inr (.inr (.inr (.inr (.inl i)))))).crest
        exact (h.beta.bin (fun _ _=> Continuous.continuousAt (f:=fun x:ℝ=> -(-Raw.orientation*x)) (by fun_prop))).prods (h.down.tears Λ.low (fun n=>pull i.1 0 (U₀ n)) (i.2.2.1,i.2.1) i.2.2.2 (Pressure.Stores.till Z.x) S.patch.L.val (Pressure.temp Z.x)) (Q:=fun i j:ℝ=>i*j) continuous_mul
    exact hh.bin (Q:=fun x=> x * α) (fun _ _=>continuousAt_id.mul_const _)
lemma wisps (u:Directions G f) (i:Coat.Miniature c f):Glints J (fun n=> (D n).Short u Q.table (K n|>.beta) o.a i) (fun n=> (D' n).Short u Q.table (H n|>.beta) o.a i):=by
    rcases i with i|i|i
    · let s:=i.1; let p:= i.2; let V n:=pull s 0 ((D n).input u); let U n:=pull s 0 (U₀ n); let f(n:ℕ):ℝ:= (D n).light u s p; let g n:= (D' n).light u s p
      have hx : Glints J f g:= (h.led U V Z.x p (febrile (Z:=Z) H₀ hz) (Oriented.choice s Z.k)).prods (oxcart H₀ H₁ hQ hz h hv U₀ he (Frill.still u) s p) (Q:=fun x y:ℝ=> x-y) (continuous_fst.sub continuous_snd)
      let C:=(D 0).enforce (2*o.a) u ((D 0).booth (rowSite S i)); have ht:= h.beta.prods (hx.prods (exhaust H₀ H₁ hQ hz h hv U₀ he s p) (Q:=fun i j=> C*i+j) (show Continuous _ from (continuous_const.mul continuous_fst).add continuous_snd)) (Q:=fun x y:ℝ=> -x*Raw.orientation*y) (show Continuous _ from (continuous_fst.neg.mul_const _).mul continuous_snd)
      by_cases hp: Inside (rowSite S i) Z.store (200*z)
      · change Glints J (fun n=>ite (Inside (rowSite S i) Z.store (200*z)) 0 _) (fun n=>ite (Inside (rowSite S i) Z.store (200*z)) 0 _); simp_rw [if_pos hp]; exact ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
      exact ht.carve (Eventually.of_forall fun i=> (if_neg hp).symm) (Eventually.of_forall fun i=> (if_neg hp).symm)
    · by_cases hp:voyage Z.store (200*z) i
      · change Glints _ (fun n=>ite (voyage Z.store (200*z) i) 0 _) (fun n=>ite (voyage Z.store (200*z) i) 0 _); simp_rw [if_pos hp]; exact ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
      exact (Draft.charges H₀ hz h (haloV hv U₀ (j:=j)) he i).crest.carve (Eventually.of_forall fun n=> (if_neg hp).symm) (Eventually.of_forall fun n=> (if_neg hp).symm)
    exact ⟨(D 0).solo u Q.table o.a i,tendsto_const_nhds,tendsto_const_nhds⟩
local notation "X"=>fun n=>kickback (D n) (K n).beta
local notation "X'"=>fun n=>kickback (D' n) (H n).beta
lemma hazy (w:Air f G) (i:ChainIndex f):Glints J (fun n=> (D n).fuel o.a (K n|>.beta) (X n w) i) (fun n=> (D' n).fuel o.a (H n|>.beta) (X' n w) i):=by
    have hA:= haloV hv U₀ (j:=j) (J:=J); let u:=(D 0).atmos w
    refine (rowsP H₀ hQ hz h hA he (Frill.still u) (restart H₀ hQ hz h hA he w) i).crest.carve ((he.and (current H₀ hz U₀ w)).mono fun n hn=> ?_) ((he.and (current H₁ hz U₀ w)).mono fun n hn=>?_)
    · exact (Polar.margins (D n) o.a (K n|>.kin) (X n w) (hz.1.symm ▸ (H₀ n).laws.data.room) hn.1 _ (hn.2 hn.1) i).symm
    exact (Polar.margins (D' n) o.a (H n|>.kin) (X' n w) (hz.1.symm ▸ (H₁ n).laws.data.room) hn.1 _ (hn.2 hn.1) i).symm
lemma mood (w:Air f G)(i:Head S)(l:Finset ℕ): Glints J (fun n=> (D n).vertex (K n).kin Q.table W o.a l Q.halo (X n w) i) (fun n=>(D' n).vertex (H n).kin Q.table W o.a l Q.halo (X' n w) i):=by
    let u:=(D 0).atmos w; have ha:∀ᶠ n in (J:Filter ℕ),(D n).liftA (K n).beta (X n w)=u:=(he.and (current H₀ hz U₀ w)).mono fun i hi=>hi.2 hi.1; have hh:∀ᶠ n in (J:Filter ℕ),(D' n).liftA (H n).beta (X' n w)=u := (he.and (current H₁ hz U₀ w)).mono fun i hi=>hi.2 hi.1
    let f(n:ℕ)(M:Epoch Λ) (b: Directions G f) (i:Head S):=i.elim (fun p=> if Packets.connected S Q.halo z p then (Z.paints M (U₀ n)).Pack M.kin Q.table l W o.a p b else 0) (Sum.elim ((Z.paints M (U₀ n)).bag M.kin o.a b) (Sum.elim (fun j=> (Z.paints M (U₀ n)).raiseAir M.kin o.a Q.table (kickback (Z.paints M (U₀ n)) M.beta w) j) ((Z.paints M (U₀ n)).detect b W o.a M.kin l)))
    refine Glints.carve (f:=fun n=> f n (K n) u i) (g:=fun n=> f n (H n) u i) ?_ (ha.mono fun n hn=> congr_arg (fun b=> f n (K n) b i) hn.symm) (hh.mono fun n hn=> congr_arg (fun b=> f n (H n) b i) hn.symm)
    rcases i with i|i|i|i
    · unfold f; simp only [Sum.elim]; split
      · exact daw H₀ H₁ hQ hz h hv U₀ he i u l
      exact ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
    · let α:=(D 0).enforce (2*o.a) u ((D 0).plaza (Raw.forcedFoot S.ratio 0 z (K 0).kin i)); exact (h.grant i (fun n=>(D n).input u)).bin (fun _ _=> Continuous.continuousAt (f:=fun x:ℝ=> x*α) (by fun_prop))
    · refine Glints.bin (f:=fun n=> (D n).farLog (K n).kin o.a Q.table (X n w) i) (g:=fun n=> (D' n).farLog (H n).kin o.a Q.table (X' n w) i) (Q:=fun x=> Real.exp x-1) ?_ (fun _ _=> (Real.continuous_exp.sub continuous_const).continuousAt); rcases i with i|i|i
      · exact (rawAge H₀ H₁ hQ hz h hv U₀ he u i).carve (ha.mono fun n hn=> congr_arg (fun u=> (D n).inhale (K n).kin o.a u i) hn.symm) (hh.mono fun n hn=> congr_arg (fun u=> (D' n).inhale (H n).kin o.a u i) hn.symm)
      · exact (wisps H₀ H₁ hQ hz h hv U₀ he u i).carve (ha.mono fun n hn=>congr_arg (fun u=> (D n).Short u Q.table (K n).beta o.a i) hn.symm) (hh.mono fun n hn=>congr_arg (fun u=> (D' n).Short u Q.table (H n).beta o.a i) hn.symm)
      exact hazy H₀ H₁ hQ hz h hv U₀ he w i
    let c n:=(D n).detect u W o.a (K n).kin l i; exact FullVolume.Shadow.flowers (f:=c) (x:=0) (Eventually.of_forall fun n=>by rw [dist_zero_right]; exact (D n).fires_at u W o.a (K n).kin l i)
end Draft
end YM.ConnectedActivityE6.Lim

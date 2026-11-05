import YM.UVExtension.Wet.Bead
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady PhysicalNext.Repeat Lotus
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Strata Strata.Polish Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
open Polar Silica Shield Score Flux Matter
variable [NeBot v] (he:0 ≤ u)(hp: StableR v R)
variable {D:(i:ι)→Leaf (R i)} (z:Constant (v:=v) D)
structure Roast (D:(i:ι)→Leaf (R i)) (C : Air f G→ℝ)(P:ι→ Molecule S→ℝ): Prop where
     receipt : Swift v P
     employs : Integrable C
     positive (z:Air f G): 0≤C z
     uv : ∀ᶠ i in v,∀ F (X:Coat (T i) F), X.x=s → X.width=U.K → X.manifest → X.χ=χ→
       ∀ K: Molecule S,(∀ l w',‖shiftV (R:=R) i X ((D i).into X w U.a Q.table l Q.halo K) w'‖ ≤ P i K*C w'.2) ∧
        ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](τ:E)(V:E→ Config G c),
         V τ=X.V → Healthy (temp X.x) ((H i).unionP K) X.V→ Mode V τ k u →∀ B':Finset (Bond f),
          let f' y:= (D i).carat B' X (V y) A Q.table K w U.a Q.halo; ∀ j≤k,∀ z,
           ‖shiftV (R:=R) i X (JetF f' j τ) z‖ ≤ P i K*C z.2

structure Wind (i:ι) (D:Leaf (R i)) (b:ℝ): Prop where
   pay : D.weight≤b
   ride (F:Forest S.ratio) (X:Coat (T i) F) (he:X.x=s)(hX:X.width=U.K)(hK:X.manifest)(hZ:X.χ=χ) (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](τ:E)(Y:E→ Config G c)(v:Air f G)(hW:Y τ=X.V)(h: Mode Y τ k u): Brush k b 1 (fun z=> D.paidU (vary X (Y z)) U.a (worldZ (vary X (Y z)) (R i).beta (course X A (R i).beta v (Y z)))) τ
include z p in
lemma whistles : ∃ F:ℝ,0≤F∧∀ i,Wind (T:=T) (w:=w) (U:=U) (s:=s) (i:=i) (χ:=χ) (k:=k) (u:=u) (A:=A) (D i) F:=by
   obtain ⟨c,hc⟩:= z.weightsC; obtain ⟨C,hC,hg⟩:= p.haj (2*U.a)
   let P:= |c| *(1+C); have hp:0≤ P:=by unfold P; positivity
   refine ⟨P,hp,fun i=> ⟨(hc i).trans ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg c) (le_add_of_nonneg_right hC))),fun F X he hx hK hZ E _ _ _ τ Y v hW hV=>?_⟩⟩
   let y z:= vary X (Y z); let u':= worldZ X (R i).beta v; let V z:= steer X A u' (Y z)
   have ht := ((p.realm.granted _ _ S (T i) _ _ (H i) (p.rails i) rfl).2 E Y F X τ he hZ hx hK hW hV).2 v|>.1
   let f:= (D i).ingredient (X.input u'); have hr:‖f‖ ≤ |c|:= ((D i).earn _).trans ((hc _).trans (le_abs_self _))
   let s':= X.plaza ((areas (R i) (T i) 0 X.B ((D i).turn.badge S))) -- Rep explicit
   have hf: Brush k (|c| *C) 1 (fun z=>f*X.enforce (2*U.a) (V z) s') τ:=by
      have h:=hg i F X hZ he E Y V _ v τ ht (by rw [mul_assoc]; exact mul_pos zero_lt_two ht.pulse)
      exact (((Brush.certified (le_refl (0:ℝ)) f).climb hr le_rfl).paints (h.2 s')|>.climb le_rfl (by rw [zero_add]))
   refine ((hf.climb (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (abs_nonneg c)) le_rfl)).shimmy ?_
   filter_upwards [ht.patch] with i' hi'; rw [show worldZ (vary X (Y i')) _ _= _ from ht.moving i']; exact (D i).canv _ _ _ _ (plastic hi' ht.pulse)
section tide
variable {i:ι}{F:Forest S.ratio}{P:Coat (T i) F} (hX:P.x=s)(hV:P.χ=χ)(hD:P.width=U.K)(hm:P.manifest)
include hX hV hD hm
lemma pearls (w':Head S→ℝ)(pw:∀ j,Lodge p i j (w' j))(hz:Wind (T:=T) (w:=w) (U:=U) (s:=s) (k:=k) (A:=A) (u:=u) (χ:=χ) i (D i) (w' ((D i).turn.badge S))) (hw:∀ j,0≤w' j)(W:Molecule S)(ph:Healthy (temp P.x) ((H i).unionP W) P.V)(U': Finset (Bond f)) (y: F.Slice G× Air f G)
     (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (τ:E)(Y:E→ Config G c) (Ht:Y τ=P.V)(h: Mode Y τ k u):
     Brush k (1*(∏ i∈W,w' i)) ((B*facescale U' y.2 ^ l)+W.card) (fun z=> (D i).carat U' P (Y z) A Q.table W w U.a Q.halo y) τ:=by
    let X:= P.wrapY y.1; let v z:=course X A (R i).beta y.2 (Y z); let t i' := steer X A (worldZ X (R i).beta y.2) (Y i'); have ht:= ((p.realm.granted _ _ S (T i) _ _ (H i) (p.rails i) rfl).2 E Y F X τ hX hV hD hm Ht h).2 y.2
    have hp (j) (hj:j∈W): Brush k (w' j) 1 (fun z=> Polar.ember (vary X (Y z)) U.a (R i) w Q.table (t z) (X.input (worldZ X (R i).beta y.2)) (v z) (Matter.own W) Q.halo j) τ:=
       (pw j).funded E F X Y _ τ _ _ hX hD hV hm h ht.1 (Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H i).supportP hj) ph) _
    let m:= (D i).turn.badge S; let W':= W.erase m
    have hh : Brush k (∏ i∈W',w' i) (W'.card:ℝ) (fun z=> Polar.floating (vary X (Y z)) U.a (R i) w Q.table (v z) (Matter.own W) Q.halo W') τ:=by
       have hf := Brush.all_prod W' _ _ _ (fun i hi=> hp i (Finset.mem_of_mem_erase hi)); simp only [sum_const,nsmul_eq_mul,mul_one] at hf; apply hf.shimmy ; filter_upwards [ht.1.patch] with z hz; unfold Polar.floating; rw [show worldZ (vary X (Y z)) _ _= t z from ht.1.moving z]
       let N' := vary X (Y z); let P' :Intake _ _ N'.x (R i) := hX.symm ▸ (H i).laws.intake
       exact Finset.prod_congr rfl fun j _=> (plastic hz ht.1.pulse).reeled (show Room _ _ _ N'.x from hX.symm ▸ (H i).laws.data.room) w Q.table (Matter.own W) Q.halo P' j (v z)
    have hz':=hz.ride F X hX hD hm hV E τ Y y.2 Ht h
    unfold Leaf.carat Leaf.chimes Leaf.floret
    split_ifs with hv
    · apply (Brush.paints (ht.2.1 U') ((hz').paints hh)).climb _ ?_; swap; · have hc: W'.card+1=W.card:= Finset.card_erase_add_one hv; rw [← hc,Nat.cast_add]; simp only [Nat.cast_one]; linarith
      exact (congr_arg ((1:ℝ)*·) (mul_prod_erase _ _ hv)).le
    change Brush k _ _ (fun z=> _* (0:ℝ)) _
    simp_rw [mul_zero]; exact Brush.zi EventuallyEq.rfl (mul_nonneg zero_le_one (prod_nonneg (fun j _=> hw j))) (add_nonneg (ht.2.1 U').pos (Nat.cast_nonneg _))
end tide
include hp p he z
lemma cameo : ∃ (f': Air f G→ℝ) (V:ι→ Molecule S→ℝ), Roast (v:=v) (D:=D) (H:=H) (χ:=χ) (k:=k) (u:=u) (A:=A) f' V :=by
    obtain ⟨f',hf,hV⟩:= opening p hp he; obtain ⟨j,hj,W'⟩:= whistles p z -- argument order
    obtain ⟨i,hi⟩:= (show ∀ᶠ i:ι in v,True from by simp).exists; let a:= (D i).turn.badge S
    have hx''(n): (D n).turn.badge S=a := congr_arg (Wing.badge · S) (z.turnC n i)
    let g(i):= if i=a then j else 0; let f (i:ι) (j):= f' i j + g j; have hg i :0≤g i:=by unfold g; split; exact hj; exact le_rfl
    have hp i j: f' i j ≤ f i j:= le_add_of_nonneg_right (hg j)
    have hJ:Swift v (fun _=>g):= Swift.nil g (u:=j) ⟨hg,(summable_of_ne_finset_zero (s:={a}) (fun i hi=>if_neg (by simpa using hi))), ((tsum_eq_single (f:=g) a (fun i hi=>by simp [g,hi])).trans (by simp [g])).le⟩
    obtain ⟨b',hr⟩:=hf.books; have hf:Swift v f:= hf.plus hJ;
    obtain ⟨t,ht,h⟩:= bulbP p he -- inspect
    let P':ℕ:=l*k; obtain ⟨F,hF,hQ,hh⟩:= fareT p he P'; have ht':0≤t:=zero_le_one.trans ht
    -- cost W multiplier 1+# + (both scaled)
    let G' (i:ι)(W: Molecule S):= ∏ j∈W,f i j; let b i W:= G' i W+(W.card:ℝ)^k*G' i W
    let M i W:= (2*t)^k*b i W; refine ⟨F,M,(hf.powerList.plus (hf.flourish k)).scales _ (by positivity),hF,hQ,?_⟩
    filter_upwards [hV,hr] with n h' hX L' X hs hu hM hχ W
    have ht (i):=hh n L' X hs hu hM hχ i; have hx:= sheet_p p he n L' X hs hu hM
    have h₁ j : p.Lodge n j (f n j):= ⟨fun V Y he hu hz hx w i=> ((h' j).value V Y he hu hz hx w i).trans (hp n j),fun E _ _ _ L X Y Z τ P r hw hu hv hm hV ht hW i=> ((h' j).funded E L X Y Z τ P r hw hu hv hm hV ht hW i).climb (hp n j) le_rfl ⟩
    have hv: j≤ f n a:= by unfold f; rw [show g a=j from if_pos rfl]; exact le_add_of_nonneg_left (hX.1 _)
    
    have hd:Wind (T:=T) (w:=w) (U:=U) (s:=s) n (k:=k) (χ:=χ) (u:=u) (A:=A) (D n) (f n ((D n).turn.badge S)):=by rw [hx'']; exact ⟨((W' n).pay).trans hv, fun F X he hu hm ht E _ _ _ τ Y v hW hV=> ((W' n).ride F X he hu hm ht E τ Y v hW hV).climb hv le_rfl⟩
    have hc(j):0≤ f n j:=(hX.1 _).trans (hp n j)
    have hw : 0 ≤ G' n W:= prod_nonneg fun _ _=> hc _
    have he : G' n W ≤ b n W:= le_add_of_nonneg_right (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hw)
    have hz :1≤ (2*t)^k:= one_le_pow₀ (by linarith : (1:ℝ) ≤ 2*t)
    constructor
    · intro v z; let y:= wound (R:=R) n X z; unfold shiftV; rw [norm_smul,Real.norm_of_nonneg (hx _)]
      have h(k)(hk:k∈W): |(X.wrapY z.1).vertex (R n) Q.table w U.a v Q.halo y k| ≤ f n k:=(h₁ k).value L' (X.wrapY z.1) hs hu hχ hM y v
      let X':=X.wrapY z.1; have hP : ‖(D n).into X w U.a Q.table v Q.halo W (z.1,y)‖ ≤ G' n W:=by
          unfold Leaf.into Leaf.premium; split; next hi=>
            rw [norm_mul]; apply le_trans _ (le_of_eq (mul_prod_erase W (f n) hi)); refine mul_le_mul ((D n).coin X' _ _|>.trans hd.pay) ?_ (norm_nonneg _) (hc _); unfold Coat.term; rw [norm_prod]; exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun k hk=> h k (mem_of_mem_erase hk))
          rw [norm_zero]; exact hw
      have hS := ((le_mul_of_one_le_right (hx z) (one_le_pow₀ (show 1 ≤ 1+‖y‖ from le_add_of_nonneg_right (norm_nonneg _)) (n:=P'))).trans (ht z))
      calc
           _ ≤ F z.2*(G' n W) := mul_le_mul hS hP (norm_nonneg _) (hQ _)
           _ ≤ _ := by rw [mul_comm (F z.2)]; exact mul_le_mul_of_nonneg_right (he.trans (le_mul_of_one_le_left (hw.trans he) hz)) (hQ _)
    intro E _ _ _ τ V hv hhV hV U' Φ j hj z
    let y:= wound (R:=R) n X z; let b':ℝ:= 1+‖y‖; let c:ℝ:=W.card; have hb':1≤b':=le_add_of_nonneg_right (norm_nonneg _)
    have hy:=pearls p hs hχ hu hM _ h₁ hd hc W hhV U' (z.1,y) E τ V hv hV
    have hB:= p.realm.roof
    let Q':=1+(B*facescale U' y^l+c); have hS: B*facescale U' y^l+c≤ Q':= le_add_of_nonneg_left zero_le_one
    have hL: ‖JetF Φ j τ (z.1,y)‖ ≤ G' n W* Q'^k:= by
       apply (hy.order j hj).trans; rw [one_mul]; apply mul_le_mul_of_nonneg_left _ hw; exact (pow_le_pow_left₀ hy.pos hS _).trans (pow_le_pow_right₀ (by unfold Q'; exact le_add_of_nonneg_right hy.pos) hj)
    unfold shiftV; rw [norm_smul,Real.norm_of_nonneg (hx _)]
    let g':= quilt (R:=R) n X z; change g' * _ ≤ _
    obtain he'|he':= W.eq_empty_or_nonempty
    · have hC : c=0 :=by unfold c; simp [he']
      have hK : Q'≤2*t*b'^l:=by unfold Q'; rw [hC,add_zero]; have hh:=h U' y; change _ ≤ t*b'^l at hh; nlinarith only [hh, ht',one_le_pow₀ hb' (n:=l)] -- positivity times
      have hh := (pow_le_pow_left₀ (hy.pos.trans hS) hK k); rw [mul_pow,← pow_mul] at hh
      calc
         _ ≤ g'*(G' n W*((2*t)^k*b'^P')) := mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hh hw)) (hx z)
         _ = (2*t)^k*G' n W*(g'*b'^P'):=by ring
         _ ≤ _ := by exact mul_le_mul (mul_le_mul_of_nonneg_left he (zero_le_one.trans hz))
                                       (ht z) (by exact mul_nonneg (hx _) (pow_nonneg (zero_le_one.trans hb') _)) (mul_nonneg (pow_nonneg (by positivity) _) (hw.trans he))
    have hC:1≤c:=by unfold c; exact_mod_cast show 1 ≤ W.card from Finset.card_pos.mpr he' -- nat pos
    have hK : Q'≤ 2*t*b'^l*c:=by unfold Q'; have hh:=h U' y; change _≤ t*b'^l at hh; nlinarith only [hh,mul_le_mul (show 1≤t from ‹1≤t›) (one_le_pow₀ hb' (n:=l)) zero_le_one ht', hC] -- nlinarith need *c
    have hh := pow_le_pow_left₀ (hy.pos.trans hS) hK k; rw [mul_pow,mul_pow,← pow_mul] at hh
    calc
       _ ≤ g'*(G' n W*((2*t)^k*b'^P' * c^k)):=mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hh hw)) (hx _)
       _ = (2*t)^k*(c^k* G' n W)*(g'*b'^P'):=by ring
       _ ≤ _:=mul_le_mul (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hw) (pow_nonneg (by positivity) _)) (ht z) (mul_nonneg (hx _) (pow_nonneg (zero_le_one.trans hb') _)) (mul_nonneg (pow_nonneg (by positivity) _) (hw.trans he))
end YM.UVExtension.Wet

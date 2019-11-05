module Control.Effect.NonDet where
newtype NonDetT m a = NonDetT { runNonDetT :: m (Maybe (a, NonDetT m a)) }

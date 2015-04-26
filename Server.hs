{-# LANGUAGE OverloadedStrings #-}
import Web.Scotty
import Data.Monoid (mconcat)
import qualified Data.Text.Lazy as B
import Sudoku

main = scotty 3000 $ do
  get "/:puzzle" $ do
    p <- param "puzzle"
    html $ B.pack ( solve p)
